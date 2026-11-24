# The path measure of a cylinder is a finite-dimensional law

For a family `κ = (κ_t)_{t ≥ 0}` of Markov kernels on `[0, 1]` satisfying the Chapman–Kolmogorov
equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`, every `x ∈ [0, 1]`, every finite set `J` of
times, with elements `j_1 < ⋯ < j_m`, and every measurable `S ⊆ [0, 1]^J`, the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
`P^κ_x` of `κ` with input `x` satisfies `P^κ_x({ω : ω|_J ∈ S}) = Q_{0, (j_1, …, j_m)}(x, e⁻¹(S))`,
where `Q` is the
[finite-dimensional kernel](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/finite-chain-kernel.md)
of `κ` and `e : [0, 1]^m → [0, 1]^J` sends `(y_1, …, y_m)` to the function `j_k ↦ y_k`. Here `x` is
the input of the kernel construction: the time-`0` marginal of `P^κ_x` is `κ_0(x, ·)`. This marginal
is the point mass at the input for every input exactly when `κ_0` is the identity kernel, which is
not assumed here; the Chapman–Kolmogorov equations alone do not imply it (the constant family
`κ_t(x, ·) = δ_0` satisfies them, and `κ_0(1, ·) = δ_0`).
