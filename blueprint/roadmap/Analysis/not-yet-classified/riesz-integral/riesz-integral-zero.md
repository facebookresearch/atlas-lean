# Riesz Integral zero

The normalized Riesz integral over the zero rectilinear cycle is zero for every element and
scalar integrand.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem rieszIntegral_zero (a : A) (f : ℂ → ℂ) :
    rieszIntegral (0 : RectilinearCycle) a f = 0
```
