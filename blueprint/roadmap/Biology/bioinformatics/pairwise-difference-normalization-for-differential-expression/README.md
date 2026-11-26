# Pairwise-difference normalization for differential expression

Gene expression measurements carry a per-sample effect shared by all genes. Global, quantile or rank normalization removes it but borrows information from differentially expressed genes, biasing two-group tests when up- and down-regulation are unbalanced. Taking differences between each gene and every other gene removes the per-sample effect exactly, and a robust summary of the resulting pairwise $t$-statistics recovers the oracle test statistic.

- [Super-delta pairwise t-statistics and the oracle statistic](super-delta-pairwise-t-statistics-and-the-oracle-statistic.md)
