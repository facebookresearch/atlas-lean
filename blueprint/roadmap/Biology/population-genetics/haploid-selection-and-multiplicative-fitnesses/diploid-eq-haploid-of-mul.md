# Diploid selection with multiplicative fitnesses as haploid selection

For real vectors `p` and `v` on a finite set of alleles with nonzero
[haploid mean fitness](../natural-selection-fisher-s-theorem-and-the-price/mean-fitness.md)
`∑_k p_k v_k ≠ 0`, and every allele `i`,
`p_i (∑_j (v_i v_j) p_j) / (∑_k ∑_l p_k p_l (v_k v_l)) = p_i v_i / (∑_k p_k v_k)`.

In terms of the named operations: the multiplicative genotype fitnesses `w_{ij} = v_i v_j` are
symmetric, so the
[marginal fitness](../natural-selection-fisher-s-theorem-and-the-price/marginal-fitness.md)
`∑_j (w_{ij} + w_{ji}) / 2 · p_j` of allele `i` is `∑_j w_{ij} p_j`, and the denominator on the
left is the
[diploid mean fitness](../natural-selection-fisher-s-theorem-and-the-price/diploid-mean-fitness.md).
So one generation of
[diploid viability selection](../natural-selection-fisher-s-theorem-and-the-price/diploid-select.md)
with fitnesses `w` gives, for every allele `i`, the same frequency `p_i v_i / ∑_k p_k v_k` as one
generation of [haploid selection](../natural-selection-fisher-s-theorem-and-the-price/select.md)
with fitnesses `v`.
