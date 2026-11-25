# Interior derivative of finite-time normalization

Assume a velocity jointly continuous on the closed finite strip and jointly C² on its open time interior. At an interior time where Burgers holds at every spatial point, with nonzero viscosity, the initial inverse normalization has ordinary derivative equal to the normalization rate. No derivative at either time endpoint is required.

## Exact statement

```lean
theorem initialInverseNormalization_hasDerivAt_finite {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a : ℝ) :
    HasDerivAt (initialInverseNormalization ν u a) (normalizationRate ν u a t) t
```

## Proof

Differentiate the averaged velocity moment and the time integral of its continuous flux rate.
