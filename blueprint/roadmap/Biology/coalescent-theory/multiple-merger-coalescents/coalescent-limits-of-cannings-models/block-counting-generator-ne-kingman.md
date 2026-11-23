# With heavy tails the limit generator differs from Kingman's for n ≥ 3

Under the [Möhle–Sagitov conditions](mohle-sagitov-lambda.md) for a sequence of Cannings models
and a finite measure `Λ` on `[0, 1]`, together with the [heavy-tail condition](heavy-tailed.md)
(through the condition `q_3 / c_N → ∫ x Λ(dx)` and a positive limit of `q_3 / c_N`, with `q_3` the
probability that three sampled lineages share a parent and `c_N` the coalescence probability),
for every `n ≥ 3` the [block-counting generator](../../coalescents/block-counting-generator.md)
of the Λ-coalescent on `0, …, n` differs from
[Kingman's](../../ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md): it
has a positive rate of triple mergers (three lineages to one), which Kingman's generator lacks.
