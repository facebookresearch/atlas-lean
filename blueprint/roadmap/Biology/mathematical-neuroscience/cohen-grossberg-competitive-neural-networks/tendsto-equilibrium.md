# Convergence to an equilibrium

**Convergence to an equilibrium** (Cohen and Grossberg 1983, Theorem 3, "Global Pattern
Formation": "Let all the hypotheses of Theorem 1 hold. Also suppose that no level sets of the
functions b_i contain an open interval and that the subsystem suprathreshold equilibrium vectors
are countable. Then each admissible trajectory converges to an equilibrium point."). Assume
hypotheses a)–d) (`StandingHypotheses`) and e)–f) (`BoundaryHypotheses`) of Theorem 1, and give
each `d_i` the inhibitory signal threshold `Γ_i ≥ 0` that the notion of a suprathreshold value
presupposes (Eq. (48)): `d_i(ξ) = 0` for `0 ≤ ξ ≤ Γ_i` and `d_i'(ξ) > 0` for `ξ > Γ_i`. Assume
that no level set of any `b_i` contains an open interval of `(0, ∞)`, and that for every set `U`
of indices the suprathreshold equilibrium vectors of the subsystem on `U` form a countable set:
the vectors `y`, zero off `U`, with `y_i > Γ_i` and
`a_i(y_i) [b_i(y_i) - ∑_{k ∈ U} c_ik d_k(y_k)] = 0` for every `i ∈ U`, that is, the equilibria
with every variable above its threshold of the system obtained from Eq. (1) by eliminating the
variables outside `U` (Sections V–VII). Let `x` be a forward solution of Eq. (1) on `[0, ∞)`
(derivative `field (x t)` within `[0, ∞)` at every `t ≥ 0`, one-sided at `0`) with every
coordinate of `x 0` positive, an admissible trajectory by Lemma 1. Then there is an equilibrium
`e` of Eq. (1), with every coordinate nonnegative and `field e = 0`, such that `x t → e` as
`t → ∞`.

## Sources

- Cohen and Grossberg (1983), Theorem 3, with the thresholds of Eq. (48).
