# Dt Output closed Form

For discrete-time state-space coefficients `(A, B, C, D)` over a nontrivially normed field, an input sequence `u` and an initial state `x₀`, the output at step `k` is `C(Aᵏ x₀ + ∑_{j < k} A^{k-1-j} B u j) + D u k`.
