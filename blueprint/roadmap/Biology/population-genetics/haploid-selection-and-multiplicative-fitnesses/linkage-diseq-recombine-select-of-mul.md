# Multiplicative selection and recombination create no disequilibrium

Consider two loci with two alleles each. If the haplotype frequencies are in linkage equilibrium,
`x(i, j) = p_i q_j`, and the haplotype fitnesses are multiplicative across loci,
`w(i, j) = a_i b_j`, then for every real `r` the haplotype frequencies obtained by one round of
[haploid selection](../natural-selection-fisher-s-theorem-and-the-price/select.md) with fitnesses
`w` followed by [random mating with recombination](../linkage-disequilibrium-and-haldane-s-map-functio/recombine.md)
fraction `r` have zero
[linkage disequilibrium](../linkage-disequilibrium-and-haldane-s-map-functio/linkage-diseq.md).

Here `p`, `q`, `a` and `b` are arbitrary real vectors. If a single-locus mean fitness
`∑_k p_k a_k` or `∑_l q_l b_l` vanishes, so does the haplotype mean fitness
`∑_h x(h) w(h) = (∑_k p_k a_k) (∑_l q_l b_l)`, and by the convention that division by `0` gives
`0` the selected frequencies, and then the recombined ones, are all `0`, which is not a haplotype
distribution. The biological domain is `0 ≤ r ≤ 1/2`, `p` and `q` nonnegative with sum `1`, and
positive fitnesses.
