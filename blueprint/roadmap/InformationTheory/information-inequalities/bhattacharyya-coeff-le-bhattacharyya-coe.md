# Data processing for the classical fidelity

Let `α` and `β` be finite types and let `S` be a row-stochastic real matrix
with rows indexed by `α` and columns by `β` (nonnegative entries, each row
summing to `1`). For nonnegative vectors `p q : α → ℝ`, the Bhattacharyya
coefficient does not decrease under `S`: `B(p, q) ≤ B(p ᵥ* S, q ᵥ* S)`,
where `B(p, q) = ∑ i, √(p i * q i)`.
