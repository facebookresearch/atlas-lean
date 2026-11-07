# Walk weight of step sequences ending at zero

The weight `W_p(k, n) = ∑ ∏_i p(x_i)` over the step sequences `x : Fin n → ℕ` with
`∑ x_i + k = n` (the walk from `k` is at `0` at time `n`). For `p(j) = P(ξ = j)` this is
`P(ξ_1 + ⋯ + ξ_n = n - k)` when `k ≤ n`, and `0` when `k > n`.
