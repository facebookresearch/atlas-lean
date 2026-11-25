# Run congr

The state at mark `n` depends only on the first `n` inputs.

In symbols: `∀ n, (∀ i < n, ω i = ω' i) → run f x₀ ω n = run f x₀ ω' n | 0, _ => rfl`.
