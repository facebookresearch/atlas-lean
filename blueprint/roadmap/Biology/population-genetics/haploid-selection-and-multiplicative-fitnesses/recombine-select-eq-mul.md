# Multiplicative haploid selection preserves linkage equilibrium

Consider two loci with two alleles each; a haplotype is a pair `(i, j)` of an allele `i` at the
first locus and an allele `j` at the second. Let the haplotype frequencies be in linkage
equilibrium, `x(i, j) = p_i q_j`, and the haplotype fitnesses be multiplicative across loci,
`w(i, j) = a_i b_j`, and let `y(g) = x(g) w(g) / ∑_h x(h) w(h)` be the result of one round of
haploid selection. Then one round of random mating with recombination fraction `r`,
`(1 - r) y(i, j) + r (∑_l y(i, l)) (∑_k y(k, j))`, gives the product
`(p_i a_i / ∑_k p_k a_k) (q_j b_j / ∑_l q_l b_l)` of the two single-locus selected frequencies, so
the population stays in linkage equilibrium.

The identity holds for all real `r`, `p`, `q`, `a` and `b`, with no nonzero mean-fitness
hypothesis: when a single-locus mean fitness `∑_k p_k a_k` or `∑_l q_l b_l` vanishes, both sides
are `0` by the convention `x / 0 = 0`. The biological domain is `0 ≤ r ≤ 1/2`, `p` and `q`
nonnegative with sum `1`, and positive fitnesses.
