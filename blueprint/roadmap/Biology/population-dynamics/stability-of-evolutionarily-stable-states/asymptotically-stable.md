# An interior evolutionarily stable state is asymptotically stable

For a finite set `ι` of strategies, a payoff matrix `A` on `ι` and an
[evolutionarily stable state](is-ess.md) `p` with `p_i > 0` for every `i`, under the replicator
equation `x_i' = x_i ((A x)_i - x · A x)` (Hofbauer and Sigmund 1998, Theorem 7.2.4, interior
case):

- every point `x₀` of the simplex is the initial value `x(0)` of a
  [solution](../replicator-dynamics/is-solution.md) for `t ≥ 0`;
- for every `ε > 0` there is `δ > 0` such that every solution with `x(0)` in the simplex and
  `‖x(0) - p‖ < δ` has `‖x(t) - p‖ < ε` for every `t ≥ 0`;
- there is `δ > 0` such that every solution with `x(0)` in the simplex and `‖x(0) - p‖ < δ`
  converges to `p`.

Here `‖v‖ = max_i |v_i|`. Evolutionarily stable states on the boundary of the simplex and boundary
rest points are not covered.
