# Heavy-tail condition for a sequence of Cannings models

For a sequence of [Cannings models](../cannings-models/cannings-model.md), the `N`-th of
population size `N`, the **heavy-tail condition** says that a triple merger is not negligible
against a pair merger: `q_3 / c_N → φ` for some `φ > 0`, where `q_3` is the
[probability](../cannings-models/merge-prob.md) that three sampled lineages share a parent and
`c_N` the [coalescence probability](../cannings-models/coal-prob.md). The ratio is read as `0` at
any `N` with `c_N = 0`, by the convention `x / 0 = 0`; as `φ > 0`, the condition therefore forces
`c_N > 0` for all large `N`, its intended domain. In offspring terms this is
`E[(ν_1)_3] / (N² c_N) → φ > 0`, with `ν_1` the
[number of offspring](../cannings-models/offspring.md) of a fixed parent and
`(ν)_3 = ν (ν - 1) (ν - 2)`: the offspring law puts enough mass on families of size of order `N`.
Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) it holds exactly when `Λ ≠ δ₀`
([criterion](heavy-tailed-iff.md)), and its failure means `q_3 / c_N → 0`, Möhle's condition for
the Kingman limit.
