#lang racket
(require redex)

;(define-language bool-any-lang
;;; the following production rules defines two non-terminals
;;; B : boolean expression
;;; C : contexts  
;  [B true
;     false
;     (∨ B B)]
;  [C (∨ C B)
;     (∨ B C)
;     hole ])
;;; given the preliminaries the following quoted S-exp are legitimate B expressions
;(define B1 (term true))
;(define B2 (term false))
;(define B3 (term (∨ true false)))
;(define B4 (term (∨ ,B1 ,B2)))
;(define B5 (term (∨ false  ,B4)))
;;; given the preliminaries the following quoted S-exp are legitimate C expressions
;
;(define C1 (term hole))
;(define C2 (term (∨ (∨ false false) hole)))
;(define C3 (term (∨ hole true)))
;
;;; here B is matched with '(∨ false true)
;(redex-match bool-any-lang
;             B
;             (term (∨ false true)))
;;; (list (match (list (bind 'B '(∨ false true)))))
;
;;; if it failes to match it prints #f
;(redex-match bool-any-lang
;             C3
;             (term (∨ true true)))
;;; (in-hole C true) says that C is to be filled with true.
;
;;; the following example matches a filled context with an expression
;;; the pattern now contains two varibles :C the context, and B , an arbitrary
;;; (sub-)expression. this use of redex-match produces a lit of two matches.
;; (list
;; (match (list (bind 'B 'false) (bind 'C '(∨ true hole))))
;; (match (list (bind 'B '(∨ true false)) (bind 'C hole))))
;
;(redex-match bool-any-lang
;             (in-hole C (∨ true B))
;             (term (∨ true (∨ true false))))
;;; rule begins with --> followed by a redex pattern and expression
;;; the pattern on the left-hand side describes redexes and their contexts
;;; the expression on the right-hand side determines the results of use such a rule on a specific expression,
;;;    the latter acts much like term but without the explict term wrapper
;;; the optional third piece is the name of the rule
;(define bool-any-red
;  (reduction-relation
;   bool-any-lang
;   (--> (in-hole C (∨ true B))
;        (in-hole C true)
;        ∨-true)
;   (--> (in-hole C (∨ false B))
;        (in-hole C false)
;        ∨-false)
;   ))
;
;;;
;(redex-match bool-any-lang
;             (in-hole C (∨ true B))
;             (term (∨ (∨ true (∨ false true) false))))
;(traces bool-any-red
;        (term (∨ (∨ true false) (∨ true true))))

(define-language bool-standard-lang
  [B true
     false
     (∨ B B)]
  [E (∨ E B)
     hole ])
(define bool-standard-red
  (reduction-relation
   bool-standard-lang
   (--> (in-hole E (∨  true B  ))
        (in-hole E true)
        ∨-true)   
   (--> (in-hole E (∨  B  false))
        (in-hole E B)
        ∨-false)
   ))

(traces bool-standard-red
        (term (∨ (∨ true false) (∨ true true))))