# Has Sum riesz Functional Calculus of Scalars

If a scalar power series has radius strictly larger than the spectral
radius of `a`, its ordered operator series sums to its Riesz
functional-calculus value.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem hasSum_rieszFunctionalCalculus_ofScalars
    (a : A) (c : ℕ → ℂ)
    (h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius) :
    HasSum (fun n : ℕ ↦ c n • a ^ n)
      (rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofScalars a c h))
```
