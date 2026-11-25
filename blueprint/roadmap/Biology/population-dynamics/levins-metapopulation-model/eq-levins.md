# For c ≥ 0, a solution with p(0) ≥ 0 equals the explicit one for t ≥ 0

For real numbers `c ≥ 0` and `e`, every [solution](is-solution-2.md) `p` of the Levins equation
`p' = c p (1 - p) - e p` with `p(0) ≥ 0` agrees on `[0, ∞)` with the [explicit solution](levins.md)
started at `p(0)`: for all `t ≥ 0`, `p(t) = p(0) e^{(c - e) t} / (1 + c p(0) φ(t))` with
`φ(t) = ∫₀ᵗ e^{(c - e) s} ds`. Nothing is claimed for `t < 0`.
