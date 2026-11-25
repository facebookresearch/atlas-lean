# Interior time derivative of the finite-time inverse profile

For nonzero viscosity, closed-strip joint continuity and open-strip joint C² regularity of the velocity, Burgers at an interior time gives the ordinary time derivative of the inverse profile there. It is the profile times the normalization rate evaluated at the spatial point; the construction anchor remains arbitrary. Neither endpoint needs a time derivative.

## Exact statement

```lean
theorem initialInverseProfile_hasDerivAt_t_finite {u : ℝ → ℝ → ℝ} {ν t T : ℝ}
    (hc : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Ioo 0 T ×ˢ univ)) (ht : t ∈ Ioo 0 T)
    (hb : ∀ x, deriv (fun s => u s x) t + u t x * deriv (u t) x =
      ν * iteratedDeriv 2 (u t) x) (hν : ν ≠ 0) (a x : ℝ) :
    HasDerivAt (fun s => initialInverseProfile ν u a s x)
      (normalizationRate ν u x t * initialInverseProfile ν u a t x) t
```

## Proof

Differentiate the exponential profile, use the normalization derivative, and cancel the spatial integral of the Burgers flux.
