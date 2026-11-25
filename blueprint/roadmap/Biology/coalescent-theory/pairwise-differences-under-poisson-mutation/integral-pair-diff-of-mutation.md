# Expected differences of a pair are θ times its mean coalescence time

Let `μ` be a probability measure on a measurable space `Ω`, let `n` be a natural number and
`θ ≥ 0`. Let `T_k` (`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate
`C(k, 2)`, and `T_2, …, T_n` are independent. Let `H` map `Ω` to the
[ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of
the `n` genes, with no condition other than that the genealogy `G = ((T_2, …, T_n), H)` be a
measurable map. Let `N` map `Ω` to mutation counts on the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy, with
conditional law given `G` under `μ` the
[mutation kernel with topology](kingman-tree-mutation-kernel.md) at `θ`: the pair `(G, N)` is
almost everywhere measurable and its law is the composition `μ_G ⊗ κ` of the law `μ_G` of `G`
with the kernel `κ`. Given the genealogy, the counts `N_b` are then independent, `N_b` Poisson
with mean `θ / 2` times the length of branch `b`.

Then for every pair `s` of genes of the sample,

`E[D_s] = θ E[τ_s]`,

where `D_s` is the [number of differences](pair-diff.md) of `s` and `τ_s` is its
[coalescence time](pair-coal-time.md), the sum of the `T_k`, `2 ≤ k ≤ n`, over the epochs during
which its two genes are in different lineages of `H`. Both are integrable: `D_s` by
[integrability of the pairwise differences](integrable-pair-diff-of-mutation.md), and `τ_s`, a
measurable function of `G`, because `|τ_s| ≤ |T_2| + ⋯ + |T_n|`.
