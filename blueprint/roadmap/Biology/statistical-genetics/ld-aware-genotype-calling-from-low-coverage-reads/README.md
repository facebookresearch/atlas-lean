# LD-aware genotype calling from low-coverage reads

Calling SNP genotypes from low-coverage shotgun sequencing by combining read likelihoods with linkage disequilibrium learned from a reference panel. Each parental haplotype is modelled as a mosaic of founder haplotypes by a left-to-right hidden Markov model, and the two parental models are combined in a factorial HMM; exact maximum-posterior multilocus genotyping is intractable, while per-locus posterior decoding is polynomial.

- [Hardness of maximum-posterior multilocus genotyping under haplotype HMMs](hardness-of-maximum-posterior-multilocus-genotyping-under-haplotype-hmms.md)
