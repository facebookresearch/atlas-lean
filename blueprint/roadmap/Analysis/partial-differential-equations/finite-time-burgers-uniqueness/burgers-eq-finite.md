# Uniqueness on a closed finite Burgers strip

For positive viscosity and any real T, two fields with the same initial values agree everywhere on [0,T] × ℝ if each is jointly continuous on the closed strip, jointly C² on the time interior, uniformly bounded on the strip, and solves Burgers in the interior. The two bounds may differ. For T < 0 the strip is empty and the conclusion is vacuous. No assumptions are imposed outside the strip.

## Exact statement

```lean
theorem burgers_eq_finite {u v : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hcu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hcv : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ 2 (Function.uncurry v) (Ioo 0 T ×ˢ univ))
    (hbu : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hbv : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |v t x| ≤ M)
    (hpu : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (hpv : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => v s x) t + v t x * deriv (v t) x = ν * iteratedDeriv 2 (v t) x)
    (h0 : ∀ x, u 0 x = v 0 x) : ∀ t ∈ Icc 0 T, ∀ x, u t x = v t x
```

## Proof

Identify each field with the same explicit initial-value construction.
