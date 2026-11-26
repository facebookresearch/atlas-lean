# Haplotype-aware diplotyping from long reads

Joint genotyping and phasing of a diploid genome from noisy long reads. Reads are bipartitioned between the two haplotypes; a layered graph of bipartitions of the reads active at each site encodes every bipartition exactly once, and adding allele assignments turns it into a hidden Markov model whose forward–backward posteriors give haplotype-aware genotype likelihoods.

- [Diploid path graph of read bipartitions](diploid-path-graph-of-read-bipartitions.md)
- [Bipartition hidden Markov model for genotype likelihoods](bipartition-hidden-markov-model-for-genotype-likelihoods.md)
