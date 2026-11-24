# For L > 0 and f′ = 0 at both ends, ∫ f″ φₙ = −(nπ/L)² ∫ f φₙ

Let `L > 0` and let `f : ℝ → ℝ` be a function such that

- `f` is differentiable at every point of `[0, L]`, and its derivative `f'` is differentiable at
  every point of `[0, L]` (two-sided, also at the ends);
- the second derivative `f''`, the derivative of `f'`, is continuous on `[0, L]`;
- `f'(0) = 0` and `f'(L) = 0`.

Then for every natural number `n`, with `φ_n(x) = cos (n π x / L)` the `n`-th [mode](cos-mode.md),

`∫₀ᴸ f''(x) φ_n(x) dx = -(n π / L)² ∫₀ᴸ f(x) φ_n(x) dx`.

The proof integrates by parts twice; the boundary terms vanish because `f'` and `φ_n'` are `0` at
both ends.
