# The approximate Hopf orbit has an ε⁴ residual in scaled time

There is a constant `C` such that for all real `ε` with `|ε| ≤ 1` and all real `s`,
`|v_ε'(s) + α(ε) v_ε(s - 1) (1 + v_ε(s))| ≤ C ε⁴`, where `v_ε` is the
[approximate orbit](hopf-approx.md) (a smooth function, so `v_ε'` is its classical derivative) and
`α(ε) = π / 2 + (3π - 2) ε² / 40` the [bifurcation parameter](hopf-param.md). So `v_ε` solves the
scaled delayed logistic equation `v'(s) = -α v(s - 1) (1 + v(s))` up to a residual of order `ε⁴`,
uniformly in time: a third-order Poincaré–Lindstedt (normal form) expansion.
