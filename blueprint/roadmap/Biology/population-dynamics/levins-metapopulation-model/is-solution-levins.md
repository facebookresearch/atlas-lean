# For c, p₀ ≥ 0, the explicit solution solves the Levins equation

For real numbers `c ≥ 0`, `e` and `p₀ ≥ 0`, the [explicit solution](levins.md)
`p(t) = p₀ e^{(c - e) t} / (1 + c p₀ φ(t))`, with `φ(t) = ∫₀ᵗ e^{(c - e) s} ds`, is a
[solution](is-solution-2.md) of the Levins equation `p' = c p (1 - p) - e p`: at every `t ≥ 0` it
has derivative `c p(t) (1 - p(t)) - e p(t)`. It starts at `p(0) = p₀`; there is no sign condition on
`e`.
