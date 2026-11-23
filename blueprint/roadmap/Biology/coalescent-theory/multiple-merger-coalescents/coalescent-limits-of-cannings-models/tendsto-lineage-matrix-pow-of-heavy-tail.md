# Heavy-tailed Cannings lineage counts have a multiple-merger limit

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) for a sequence of Cannings models
and a finite measure `Λ` on `[0, 1]`, together with the [heavy-tail condition](heavy-tailed.md),
for every `n` and `t ≥ 0`: `Λ ≠ δ₀`, the triple-merger rate `λ_{3,3} = ∫ x Λ(dx)` is positive, and
`Π_N^⌊t / c_N⌋ → exp(t G_Λ)` as `N → ∞`, where `Π_N` is the one-generation
[transition matrix](../cannings-models/lineage-matrix.md) of the ancestral lineage count on
`0, …, n`, `c_N` the [coalescence probability](../cannings-models/coal-prob.md) and `G_Λ` the
[block-counting generator](../../coalescents/block-counting-generator.md) of the Λ-coalescent: the
time-rescaled ancestral lineage count converges to the Λ-coalescent's block-counting process
([convergence theorem](tendsto-lineage-matrix-pow.md)).
