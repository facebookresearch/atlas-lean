# Heat evolution of the finite-time inverse profile

Under closed-strip joint continuity, open-strip joint C² regularity, nonzero viscosity and Burgers at an interior time, the inverse profile has an ordinary time derivative equal to viscosity times its second spatial derivative. This is an interior-time heat equation and does not assert derivatives at the initial or terminal time.

## Exact statement

```lean
theorem initialInverseProfile_hasDerivAt_heat_finite {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialInverseProfile ν u a s x)
      (ν * iteratedDeriv 2 (initialInverseProfile ν u a t) x) t
```

## Proof

Combine the profile time-derivative identity with its second spatial derivative formula.
