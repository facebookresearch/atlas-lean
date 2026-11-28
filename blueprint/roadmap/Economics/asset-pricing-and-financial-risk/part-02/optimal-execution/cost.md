# Cost

For a real path `x₀, …, x_N`, the quadratic liquidation cost is the sum over `0 ≤ k < N`
of `Δ [η ((x_{k+1} − x_k)/Δ)² + κ x_k²]`. The inventory penalty uses the **left** endpoint.
The optimisation problem takes `N ≥ 1`, `Δ > 0`, `η > 0`, `κ ≥ 0`, `x₀ = X₀` and `x_N = 0`.
The sum itself imposes no endpoint constraints and is zero for `N = 0` or `Δ = 0` (real
division by zero is zero).
