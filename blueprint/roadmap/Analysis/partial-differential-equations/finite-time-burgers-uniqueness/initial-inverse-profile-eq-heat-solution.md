# Heat identification on a finite Burgers lifespan

Let ν > 0 and T ≥ 0. A velocity jointly continuous on [0,T] × ℝ, jointly C² on (0,T) × ℝ, uniformly bounded on the closed strip, and satisfying Burgers throughout the interior has its normalized inverse profile equal to heat evolution of its initial exponential profile. Equality holds throughout the closed strip, including both endpoint traces and the zero-length strip. Values outside the strip are unrestricted.

## Exact statement

```lean
theorem initialInverseProfile_eq_heatSolution_finite {u : ℝ → ℝ → ℝ} {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x,
      initialInverseProfile ν u a t x = heatSolution (initialHeatProfile ν (u 0) a) (ν * t) x
```

## Proof

Apply whole-line heat uniqueness on each shorter interior strip, then use closed-strip continuity for the terminal trace.
