# Ordered velocities and the ratio of initial heat profiles

For positive viscosity and continuous real velocities u ≤ v pointwise, the ratio of their positive initial heat profiles, using one common arbitrary anchor, is nondecreasing in space. The velocities need not be bounded and no initial derivative is assumed.

## Exact statement

```lean
theorem initialHeatProfile_ratio_monotone {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {ν : ℝ} (hν : 0 < ν)
    (h : ∀ x, u x ≤ v x) (a : ℝ) :
    Monotone (fun x => initialHeatProfile ν u a x / initialHeatProfile ν v a x)
```

## Proof

Differentiate the positive profile ratio and use the sign of v−u.
