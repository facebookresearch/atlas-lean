# Binomial z-score approximation to the motif conservation score

The conserved count
`k` of a motif with `N` occurrences, standardized under `Bin(N, p)`:
`(k - N p) / √(N p (1 - p))`. This is an approximation to Xie et al.'s MCS, not their
exact score.
