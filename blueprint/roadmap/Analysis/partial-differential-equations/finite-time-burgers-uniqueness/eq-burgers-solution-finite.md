# Identification of finite-lifespan Burgers solutions

For positive viscosity and any real finite horizon, a bounded classical Burgers competitor continuous on the closed strip and jointly C² on its open time interior equals the explicit Cole–Hopf construction from its initial velocity. Equality includes the initial and terminal time; the PDE and time derivatives are only required in the interior. The normalization anchor is arbitrary. A negative horizon gives an empty strip and a vacuous conclusion.

## Exact statement

```lean
theorem eq_burgersSolution_finite {u : ℝ → ℝ → ℝ} {ν T : ℝ} (hν : 0 < ν)
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ))
    (hb : ∃ M, ∀ t ∈ Icc 0 T, ∀ x, |u t x| ≤ M)
    (hpde : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun s => u s x) t + u t x * deriv (u t) x = ν * iteratedDeriv 2 (u t) x)
    (a : ℝ) : ∀ t ∈ Icc 0 T, ∀ x, u t x = burgersSolution ν (u 0) a t x
```

## Proof

Identify the inverse profile with heat evolution and recover velocity from its spatial logarithmic derivative.
