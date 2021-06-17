#lang racket
(require redex)
;;; ISWIM is based on SECD machine, which is defined as
;;;    https://en.wikipedia.org/wiki/ISWIM
(define-language iswim
  ;; M denotes the ISWIM expressions (with alias of N,L,K), which includes
  ;; X         variables,
  ;; (λ X M)   lambda expressions,
  ;; (M M )    applications,
  ;; b         basic constants
  ;; (o2 M M ) (o1 M) primitive operations
  
  ((M N L K )    X (λ X M) (M M ) (M M) b (o2 M M ) (o1 M))
  (o             o1 o2)
  (o1            add1 sub1 iszero sqrt)
  (o2            + - * ^)
  (b             number)
  ;; 
  ((V U W)      b X ( λ X M))
  ;; question? what's E rule for?
  ;; pp57, a context is an expression with a hole.
  (E             hole (V E) (E M) (o V ... E M ...))
  ((X Y Z)       variable-not-otherwise-mentioned))

;; meta functions
;;   the partial delta function which
;;   maps o1 o2 with constants into a value
(define-metafunction iswim
  [(δ (iszero 0)) (λ x (λ y x))]
  [(δ (iszero b)) (λ x (λ y y))]
  [(δ (add1 b)) ,(add1 (term b))]
  [(δ (sub1 b)) ,(sub1 (term b))]
  [(δ (sqrt b)) ,(sqrt (term b))]
  [(δ (+ b_1 b_2)) ,(+ (term b_1) (term b_2))]
  [(δ (- b_1 b_2)) ,(- (term b_1) (term b_2))]
  [(δ (* b_1 b_2)) ,(* (term b_1) (term b_2))]
  [(δ (^ b_1 b_2)) ,(expt (term b_1) (term b_2))])
(define-term
  ☰ (λ x (λ y x)))
(define-term 
  ☷  (λ x (λ y y)))
  
;; iswim.rkt> (term (δ (iszero 0)))
;; '(λ x (λ y x))
;; Substitution rule
;; subst [expression] [pattern] [replacement]
(define-metafunction iswim
  ;; 1. X_1 bound, so don't continue in λ body
  [(subst (λ X_1 any_1) X_1 any_2)
   (λ X_1 any_1)]
  ;; 2. do capture avoiding substitution by generating a fresh name
  [(subst  (λ X_1 any_1) X_2 any_2)
   (λ X_3
     (subst (subst-var any_1 X_1 X_3) X_2 any_2))
   (where X_3 ,(variable-not-in (term (X_2 any_1 any_2))
                                (term X_1)))]
  ;; 3. replace X_1 with any_1
  [(subst X_1 X_1 any_1) any_1]
  ;; the last two cases just recur on the tree strcuture of the term
  ;; (any ...) matches a list, so we do subst on each of the element in the list
  [(subst (any_2 ...) X_1 any_1)
   ((subst any_2 X_1 any_1) ...)]
  ;; if the subst fails, keep it as is.
  [(subst any_2 X_1 any_1) any_2])
;; reduce the exp time subst by using auxiliary meta-function

(define-metafunction iswim
  [(subst-var (any_1 ...) variable_1 variable_2)
   ((subst-var any_1 variable_1 variable_2) ...)]
  [(subst-var variable_1 variable_1 variable_2) variable_2]
  [(subst-var any_1 variable_1 variable_2) any_1])

;; now define reduction relation
(define iswim-red
  (reduction-relation
   iswim
   (--> (in-hole E ((λ X M) V))
        (in-hole E (subst M X V))
        βv)
   (--> (in-hole E (o b ...))
        (in-hole E (δ (o b ...)))
        δv)
   ;; following rules are just to show t/f value
   (--> (λ x (λ y x))
        true
        true1)
   (--> (λ x (λ y y))
        false
        false2)))
(define iswim-standard
  (reduction-relation
   iswim
   (v ((λ X S) V) (subst S X V)  βv)
   (v (o b ...) (δ (o b ...)) δv)
   with
   [(--> (in-hole E S)
         (in-hole E T))
         (v S T)]))

;; (traces iswim-standard
;;       (term (λ x (+ (add1 x) 9) 5)))
;; (traces iswim-standard
;;       (term (+ 3 2 )))
  
(define (test-suite)
  (test-->> iswim-red
            (term (iszero 0) )
            (term true))
  (test-->> iswim-red
            (term (iszero 4) )
            (term false))
  (test-->> iswim-red
            (term ((λ x1 (sub1 x1)) (+ 3 2 )))
            (term 4))
  (test-results))
(test-suite)
;;(render-redution-relation iswim-red)
