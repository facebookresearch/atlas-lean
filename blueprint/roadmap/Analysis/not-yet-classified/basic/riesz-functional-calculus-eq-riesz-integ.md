# Riesz Functional Calculus eq riesz Integral rep

Every admissible grid in the chosen representative analytic domain gives the same
functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_eq_rieszIntegral_rep (a : A)
    (f : HolomorphicNearSpectrum a) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) (f.analyticDomain a)) :
    rieszFunctionalCalculus a f = rieszIntegral D.toCycle a (f.rep a)
```
