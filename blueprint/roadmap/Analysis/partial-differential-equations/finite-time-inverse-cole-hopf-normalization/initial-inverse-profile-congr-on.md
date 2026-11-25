# Finite-time locality of the inverse profile

If two velocity fields agree on the closed strip [0,T] × ℝ, their initial-time inverse profiles agree at every time in [0,T] and every spatial point, for arbitrary viscosity and anchor. No continuity, boundedness or equation hypothesis is required. Membership of the evaluated time in the strip supplies its nonemptiness.

## Exact statement

```lean
theorem initialInverseProfile_congrOn {u v : ℝ → ℝ → ℝ} {T : ℝ}
    (h : EqOn (Function.uncurry u) (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (ν a : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    initialInverseProfile ν u a t x = initialInverseProfile ν v a t x
```

## Proof

Restrict the time integral in the normalization to [0,t] and use equality of the spatial velocity slices.
