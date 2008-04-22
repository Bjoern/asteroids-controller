;;asteroids 
;;Author: Bjoern Guenzel
;;Date: 2008-04-20
;;derived from the demo client for the c't asteroids challenge 2008
;;License:GNU Lesser General Public License Version 3 (LGPLv3), see http://www.gnu.org/licenses/lgpl.html 


;connection settings

(define host "127.0.0.1")
(define send-port 1979)
(define receive-port 2008)


(define log-level-debug 4)
(define log-level-info 3)

(define log-level log-level-debug)

;mame keys
(define key-hyperspace 1)
(define key-fire 2)
(define key-thrust 4)
(define key-right 8)
(define key-left #x10)
(define key-start #x20);requires patch, see wiki of asteroids challenge

;vector language constants
(define number-addresses (list #xADD #xB2E #xB32 #xB3A #xB41 #xB48 #xB4F #xB56 #xB5B #xB63));numbers 0 to 9

;utility functions
(define (add2 n) (+ n 2))
(define (<< n m) (arithmetic-shift n m))
(define (>> n m) (arithmetic-shift n (- m)))
(define 10-bits #x3ff)
(define (puts . msgs) (for-each display msgs) (newline))
(define (log level msgs) (if (>= log-level level) (apply puts msgs)))
(define (debug . msgs) (log log-level-debug msgs))
(define (info . msgs) (log log-level-info msgs))
(define (list-index obj l) ;used to convert number addresses to numbers
  (let ((tail  (memq obj l)))
    (if tail
	(- (length l) (length tail))
	#f)))


;accessors
(define (ship frame) (if frame (caddr frame) #f))

(define (interpret-frame-buffer buffer)
  (letrec ((lives 0)
	   (score 0)
	   (ship #f)
	   (asteroids '())
	   (ufo #f)
	   (bullets '())
	   (stack '());for subroutines below address 512 - unlikely to happen
	   (address 0);next address to interpret
	   (gsf 0);gsf is a state value of the vector language interpreter
	   (ray-x 0)
	   (ray-y 0)
	   (ship-coordinates #f)
	   (ship-first-side #f);dx and dy of vector that draws first side of ship
	   (bit->sign;convert sign bit to -1 or 1
	    (lambda (bit) (if (= 1 bit) -1 1)))
	   (read-word ;read word at address
	    (lambda () 
	      (let* ((low-byte (bytes-ref buffer address))
		     (high-byte (bytes-ref buffer (add1 address)))
		     (word (bitwise-ior low-byte 
					(<< high-byte 8))))
		(debug "line " address " read-word low: " 
		       (number->string low-byte 2) " high: " 
		       (number->string high-byte 2) " word " (number->string word 2))
		(set! address (add2 address));next address
		word)))
	   (interpret
	    (lambda ()
	      (let* 
		  (
		   (word (read-word))
		   (op (>> word 12)))
		(case op
		  
		  ((0 1 2 3 4 5 6 7 8 9);VCTR - long vector
	      		   (let* ((divisor (>> 512 (bitwise-and (+ op gsf) #xF)))
			  (sign-y (bit->sign (bitwise-and 1 (>> word 10))))
			  (y (bitwise-and word 10-bits))
			  (2nd-word (read-word))
			  (z (>> 2nd-word 12));brightness
			  (sign-x (bit->sign (bitwise-and 1 (>> 2nd-word 10))))
			  (x (bitwise-and 2nd-word 10-bits))
			  (dx (* sign-x (quotient x divisor)))
			  (dy (* sign-y (quotient y divisor))));delta x
			     (debug "VCTR op: " op " z: " z " dx: " dx " dy: " dy " gsf: " gsf " divisor: " divisor " x: " x " y: " y " word: " (number->string word 2) " 2nword: " (number->string 2nd-word 2))
			     (if (<= address 1024);try to understand what is being drawn
				 (cond 
			      
				  ((and (= dx 0) (= dy 0) (= z 15));bullet
				   (debug "bullet")
				   (set! bullets (cons (list ray-x ray-y) bullets)))
				  
				  ((and (= z 0) (< 0 (+ (* dx dx ) (* dy dy))));assume spaceship, vector from center
				   (info "spaceship")
				   (set! ship-coordinates (cons ray-x ray-y)))
				  
				  ((and (= z 12) (= op 6) (> (+ (* dx dx) (* dy dy)) 0));long side of ship?
					;direction of ship = long side1 - long side2 (I hope)
				   (if ship-first-side ;we already saved the first side
				       (let* ((d-ship-x (- (car ship-first-side) dx))
					      (d-ship-y (- (cdr ship-first-side) dy)))
					 (set! ship (list ship-coordinates (cons d-ship-x d-ship-y)))
					 (set! ship-first-side #f)
					 (set! ship-coordinates #f))			
				       (set! ship-first-side (cons dx dy))))))
			     (set! ray-x (+ ray-x dx))
			     (set! ray-y (+ ray-y dy))))
		  
		  ((#xA) ;LABS - position ray
		   (let* ((y (bitwise-and 10-bits word))
			  (2nd-word (read-word))
			  (new-gsf (>> 2nd-word 12))
			  (x (bitwise-and 10-bits word)))
		     (debug "LABS x: " x " y: " y " gsf " gsf)
		     (set! ray-x x)
		     (set! ray-y y)
		     (set! gsf new-gsf)))
		  
		  ((#xB)
		   (debug "HALT"));HALT - end vector program
		  
		  ((#xC);JSLR - jump to subroutine (push address on stack)
		   (let ((a (bitwise-and #xFFF word)));target address, first 12 bits
		     (debug "JSLR " a)
		     (cond 
		      ((<= a 512);address in RAM, not ROM
		       (set! stack (cons address stack))
		       (set! address (* 2 a)))
		      (else ;address in ROM, compare with known subroutines
		       (case a
			 ((#x8F3 #x8FF #x90D #x91A);asteroids of type 1,2,3 and 4
			  (debug "asteroid type " a)
			  (set! asteroids (cons (list ray-x ray-y gsf a) asteroids)))
			 ((#x929) ;UFO - we assume there can only be one
			  (debug "ufo")
			  (set! ufo (list ray-x ray-y gsf)))
			 ((#x852) (debug "copyright"));copyright - not interesting
			 ((#x880 #x896 #x8B5 #x8D0);explosions - we don't interpret them yet
			  (debug "explosion"))
			 ((#xA6D);vertical spaceship, indicating lives
			  (debug "life")
			  (set! lives (add1 lives)))
			 ((#xADD #xB2E #xB32 #xB3A #xB41 #xB48 #xB4F #xB56 #xB5B #xB63);numbers 0 to 9 (not sure how to use number-addresses here)
			  (debug "number")
			  (cond (= 1 gsf);score (else it would be the highscore)
				(debug "score")
					;TODO  (let ((digit (list-index a number-addresses)))
					;    (set! score (+ (* 10 score) digit))))))))))
				)))))))  
		  ((#xD);RTSL return from subroutine
		   (debug "RTSL")
		   (set! address (car stack));go to address on stack
		   (set! stack (cdr stack)));remove it from stack
		  
		  ((#xE);JMPL
		   (let ((a (bitwise-and #xFFF word)));target address, first 12 bits
		     (debug "JMPL " a)
		     (set! address (* 2 a))));XXX fails if address is in ROM - should throw exception
		  
		  ((#xF);SVEC - short vector
		   (debug "SVEC")
		   (let* ((sf (bitwise-ior 
			       (bitwise-and 1 (>> word 11))
			       (bitwise-and 2 (>> word 3))))
			  (divisor (>> 128 (bitwise-and 3 (+ sf gsf))));not sure if this is correct
			  (sign-y (bit->sign (bitwise-and 1 (>> word 10))))
			  (sign-x (bit->sign (bitwise-and 1 (>> word 3))))
			  (z (bitwise-and #xF (>> word 4)));brightness
			  (y (bitwise-and word #x3FF))
			  (x (<< (bitwise-and word 3) 8))
			  (dx (* sign-x (quotient x divisor)))
			  (dy (* sign-y (quotient y divisor))))
		     (debug "SVEC dx: " dx " dy: " dy " sf: " sf " divisor: " divisor " z: " z) 
		     (set! ray-x (+ ray-x dx))
		     (set! ray-y (+ ray-y dy)))))
		(cond 
		 ((or (= op #xB) (> address 1024))
		  (debug "end interpret, address: " address ", op: " op)
		  (list lives score ship asteroids ufo bullets));return frame interpretation
		 (else (interpret)))))))
    (interpret)))
	      
(define (print-buffer buffer)
  (letrec ((print-lines (lambda (line)
			  (cond ((< line (bytes-length buffer))
				 (debug "line " line 
					" " (number->string (bytes-ref buffer line) 16)
					" " (number->string (bytes-ref buffer (add1 line)) 16))
				 (print-lines (add2 line)))))))
    (print-lines 0)))

(define socket (udp-open-socket host #f))

(udp-bind! socket host receive-port)
(udp-connect! socket host send-port)
(udp-close socket)

(define buffer (make-bytes 1024)); we receive at most 1KB of vector data


(define (comm-loop socket)
  (let ((test-message (string->bytes/utf-8 "ctmame")))
    (udp-send socket (bytes-append test-message (bytes 22 255)))
    (if (car (call-with-values (lambda () (udp-receive!* socket buffer)) list))
	(interpret-frame-buffer buffer)
	#f)))

(comm-loop socket)
(ship (comm-loop socket))
(define (read-frames n)
  (cond ((> n 0) 
	 (let ((frame (comm-loop socket)))
	  (puts "frame " n ": " frame " ship: " (ship frame))
	  (if (not (and frame (ship frame))) (read-frames (- n 1)))))))

(read-frames 100)
(puts "frame " 1 ": " (comm-loop socket))
(print-buffer buffer)
(info "lala")

(ship (interpret-frame-buffer buffer))
(number->string #x3ff 2)

(caddr '(1 2 3 4))