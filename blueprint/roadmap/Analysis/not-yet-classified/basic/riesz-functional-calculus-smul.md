# Riesz Functional Calculus smul

The Riesz functional calculus preserves complex scalar multiplication.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszFunctionalCalculus_smul (a : A) (c : ℂ)
    (f : HolomorphicNearSpectrum a) :
    rieszFunctionalCalculus a (c • f) = c • rieszFunctionalCalculus a f
```
