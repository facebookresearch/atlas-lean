# Path-measure kernel of a Chapman–Kolmogorov family

For a family `κ = (κ_t)_{t ≥ 0}` of Markov kernels on `[0, 1]` satisfying the Chapman–Kolmogorov
equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`, the Markov kernel from `[0, 1]` to the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md) that sends `x` to
the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
`P^κ_x` of `κ` with input `x`; it is a kernel because
[`x ↦ P^κ_x` is measurable](measurable-path-measure.md). Here `x` is the input of the kernel
construction: the time-`0` marginal of `P^κ_x` is `κ_0(x, ·)`. This marginal is the point mass at
the input for every input exactly when `κ_0` is the identity kernel, which is not assumed here; the
Chapman–Kolmogorov equations alone do not imply it (the constant family `κ_t(x, ·) = δ_0` satisfies
them, and `κ_0(1, ·) = δ_0`).
