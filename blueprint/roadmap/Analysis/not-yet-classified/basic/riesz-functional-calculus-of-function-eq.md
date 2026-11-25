# Riesz Functional Calculus of Function eq riesz Integral

Evaluate the functional calculus by the Riesz integral of a globally
defined function analytic on an open neighborhood of the spectrum.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_ofFunction_eq_rieszIntegral
    (a : A) (g : ℂ → ℂ) {G : Set ℂ}
    (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    (hg : DifferentiableOn ℂ g G) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a g
          ((hg.analyticOnNhd hG).mono hσG)) =
      rieszIntegral D.toCycle a g
```
