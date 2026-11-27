# Tajima's E π = θ under Poisson mutation, given Exp(1) pair times

Let `μ` be a probability measure on a measurable space `Ω`, let `n ≥ 2` and `θ ≥ 0`. Let `T_k`
(`k ∈ ℕ`) be
[Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) of a
sample of size `n` under `μ`: for `2 ≤ k ≤ n`, `T_k` has the exponential law with rate
`C(k, 2)`, and `T_2, …, T_n` are independent. Let `H` map `Ω` to the
[ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of
the `n` genes, such that the genealogy `G = ((T_2, …, T_n), H)` is a measurable map. Let `N` map
`Ω` to mutation counts on the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy, with
conditional law given `G` under `μ` the
[mutation kernel with topology](kingman-tree-mutation-kernel.md) at `θ`: the pair `(G, N)` is
almost everywhere measurable and its law is the composition `μ_G ⊗ κ` of the law `μ_G` of `G`
with the kernel `κ`, so that mutations fall at rate `θ / 2` per lineage. Suppose moreover that
for every pair `s` of genes of the sample, the [coalescence time](pair-coal-time.md) `τ_s` (the
sum of the `T_k`, `2 ≤ k ≤ n`, over the epochs during which the two genes of `s` are in different
lineages of `H`) has the exponential law with rate `1` under `μ`.

Then the
[mean number of pairwise differences](../segregating-sites-and-pairwise-differences/mean-pair-diff.md)
`π = C(n, 2)⁻¹ ∑_s D_s`, the sum running over the pairs `s` of the sample and `D_s` being the
[number of differences](pair-diff.md) of `s`, satisfies

`E π = θ`.

The other hypotheses of
[Tajima's expected pairwise differences](../segregating-sites-and-pairwise-differences/integral-mean-pair-diff.md),
that each `D_s` is [integrable](integrable-pair-diff-of-mutation.md) with
[conditional mean](cond-exp-pair-diff-of-mutation.md) `θ τ_s` given `G`, follow from the mutation
model.
