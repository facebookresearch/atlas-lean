# Diploid selection with multiplicative fitnesses as haploid selection

For real vectors `p` and `v` on a finite set of alleles with nonzero haploid mean fitness
`∑_i p_i v_i ≠ 0`, and every allele `i`,
`p_i (∑_j (v_i v_j) p_j) / (∑_i ∑_j p_i p_j (v_i v_j)) = p_i v_i / (∑_i p_i v_i)`: with
multiplicative genotype fitnesses `w_{ij} = v_i v_j`, one generation of diploid viability selection
(marginal fitness `∑_j w_{ij} p_j`) gives the same frequencies as one generation of haploid
selection with fitnesses `v`.
