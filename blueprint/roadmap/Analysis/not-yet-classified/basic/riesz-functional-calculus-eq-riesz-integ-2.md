# Riesz Functional Calculus eq riesz Integral of germ eq

Evaluate the functional calculus using any global representative of a
spectrum germ and any admissible contour in an open domain of analyticity.
This removes both representative and contour choices from
`rieszFunctionalCalculus`.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_eq_rieszIntegral_of_germ_eq
    (a : A) (f : HolomorphicNearSpectrum a) (g : ℂ → ℂ)
    (hgerm : (g : SpectrumGerm a) = f.1) {G : Set ℂ}
    (hG : IsOpen G) (hσG : spectrum ℂ a ⊆ G)
    (hg : DifferentiableOn ℂ g G) (D : GridFilling)
    (hD : D.IsAdmissibleFor (spectrum ℂ a) G) :
    rieszFunctionalCalculus a f = rieszIntegral D.toCycle a g
```
