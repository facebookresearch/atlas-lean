# Explicit Euler for the index-one system (headline)

Let `D` be invertible, the forcing
`f, g` be `C²`, `t₀ < T`, and `(x₀, y₀)` be consistent at `t₀`. Then (1) the descriptor system has
a solution on `[t₀, T]` through `(x₀, y₀)`; and (2) there is a constant `K ≥ 0` such that, for
every solution `(x, y)` on `[t₀, T]` with `x t₀ = x₀`, every step `h ∈ (0, T - t₀]`, every
explicit-Euler sequence `X` of the reduced field with step `h` (any initial value `X 0`) and every
`k` with `k h ≤ T - t₀`, the state error at `t₀ + k h` is at most
`exp (L (T - t₀)) ‖X 0 - x₀‖ + K h`, and the error of the algebraic value reconstructed at the
same time sample is at most `‖D⁻¹ * C‖` times that bound.
