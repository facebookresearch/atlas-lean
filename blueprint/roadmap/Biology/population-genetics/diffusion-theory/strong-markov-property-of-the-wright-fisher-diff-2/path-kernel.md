# Path-measure kernel of a Chapman–Kolmogorov family

For a family `κ = (κ_t)_{t ≥ 0}` of Markov kernels on `[0, 1]` satisfying the Chapman–Kolmogorov
equations `κ_{s + t}(x, ·) = ∫ κ_t(y, ·) κ_s(x, dy)`, the Markov kernel from `[0, 1]` to the
[sample paths](../construction-of-the-neutral-wright-fisher-diffus/sample-path.md) that sends `x` to
the
[path measure](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)
`P^κ_x` of `κ` from `x`; it is a kernel because
[`x ↦ P^κ_x` is measurable](measurable-path-measure.md).
