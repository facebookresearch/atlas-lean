# Restart of a classical Burgers field

Let the viscosity be positive. Suppose a field is jointly continuous on the nonnegative half-plane, jointly C² on the positive half-plane, and solves Burgers at every positive time. Assume a uniform spatial velocity bound on each finite closed time strip, with the bound allowed to depend on the strip. At any nonnegative restart time, the later field equals the Cole–Hopf construction from that time slice, with arbitrary normalization anchor. Both elapsed time and restart time may be zero.

## Exact statement

```lean
theorem burgers_restart {u : ℝ → ℝ → ℝ} {ν : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Ici 0 ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioi 0 ×ˢ univ))
    (hb : ∀ T, 0 ≤ T → ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t, 0 < t → ∀ x,
      deriv (fun r => u r x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a s t x : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    u (s + t) x = burgersSolution ν (u s) a t x
```

## Proof

Translate time, verify the same continuity, regularity, equation and strip-bound hypotheses, and apply classical uniqueness.
