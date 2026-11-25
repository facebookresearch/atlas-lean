# Continuity of the inverse profile on a finite strip

For T ≥ 0 and a velocity jointly continuous on [0,T] × ℝ, the initial-time inverse profile is jointly continuous on that same closed strip, for arbitrary viscosity and spatial anchor. No PDE or derivative hypothesis is used.

## Exact statement

```lean
theorem initialInverseProfile_continuousOn_finite {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (ν a : ℝ) :
    ContinuousOn (Function.uncurry (initialInverseProfile ν u a)) (Icc 0 T ×ˢ univ)
```

## Proof

Clamp the time variable to the closed strip, apply initial-time profile continuity to the clamped field, and use finite-time locality.
