# Example: a source built from a binary-weight target fits that target

Let `β ≠ 0` and let `M` be a [drift model](../patterson-s-f-statistics/drift-model.md) on a measure
`μ`, with eight edges and six populations, whose lineage weights `w` are the
[reversed table](reversed-weight.md) with parameter `β` and whose edge lengths are all `1`. Take
`S₀ = 0`, the target `T = 1`, `S₁ = 2` and the right populations `(R₀, R₁, R₂) = (3, 4, 5)`. Then

- with the sources `(S₀, S₁)`, the only solution of the system of the
  [source matrix](qp-adm-source-matrix.md) and the [target vector](qp-adm-target-vector.md) of `T`
  is the weight `1 / β` on `S₁`;
- the [qpWave matrix](../abba-baba-test-and-f-statistic-estimators/f4-matrix.md) of the left
  populations `(S₀, T, S₁)` has rank exactly `1`;
- the source is built from the target: `w S₁ = β w T + (1 - β) w S₀ + u`, where `u` is `1` on
  edge `3` and `0` on the other edges (drift private to `S₁`); for `0 < β ≤ 1` the table is the
  graph in which `S₁` descends from a mixture of `T` and `S₀`, while for other `β` it is only a
  real weight table;
- every lineage weight of `T` is `0` or `1`;
- for no real `γ` is `w T = γ w S₁ + (1 - γ) w S₀`.

For `β = 1/2` the fitted weights are `-1` on `S₀` and `2` on `S₁`.
