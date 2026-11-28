# Lyapunov stability for the Levins equation

For real numbers `c` and `e`, a real `a` and a set `D` of reals, `a` is Lyapunov stable for the
solutions of the Levins equation `p' = c p (1 - p) - e p` starting in `D` if for every `ε > 0`
there is `δ > 0` such that every [solution](is-solution-2.md) `p` with `p(0) ∈ D` and
`|p(0) - a| < δ` satisfies `|p(t) - a| < ε` for all `t ≥ 0`. Solutions starting outside `D` are not
considered, and `a` need not lie in `D` or be an equilibrium.
