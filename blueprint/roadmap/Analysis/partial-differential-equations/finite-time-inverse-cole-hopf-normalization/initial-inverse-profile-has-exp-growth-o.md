# Exponential growth of the finite-time inverse profile

For T ≥ 0, assume joint continuity of the velocity on [0,T] × ℝ and one bound for its absolute value throughout that strip. The inverse profile then has a uniform exponential spatial-growth bound on the strip, for arbitrary viscosity and anchor. The statement uses the totalized real division in the profile definition, so viscosity need not be nonzero.

## Exact statement

```lean
theorem initialInverseProfile_hasExpGrowthOnStrip_finite {u : ℝ → ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M) (ν a : ℝ) :
    MathlibExt.Analysis.PDE.HeatWholeLine.HasExpGrowthOnStrip (initialInverseProfile ν u a) T
```

## Proof

Apply the strip growth estimate to the time-clamped velocity and transfer it back by finite-time locality.
