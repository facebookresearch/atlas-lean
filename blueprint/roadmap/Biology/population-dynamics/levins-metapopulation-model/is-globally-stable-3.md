# Global stability for the Levins equation

For real numbers `c` and `e`, a real `a` and a set `D` of reals, `a` is globally
(asymptotically) stable on `D` for the Levins equation `p' = c p (1 - p) - e p` if it is
[Lyapunov stable](is-lyapunov-stable-2.md) for the solutions starting in `D` and
[attracts](is-globally-attracting-2.md) every solution starting in `D`: for every `ε > 0` there is
`δ > 0` such that every [solution](is-solution-2.md) `p` with `p(0) ∈ D` and `|p(0) - a| < δ`
satisfies `|p(t) - a| < ε` for all `t ≥ 0`, and every solution with `p(0) ∈ D` tends to `a` as
`t → ∞`.
