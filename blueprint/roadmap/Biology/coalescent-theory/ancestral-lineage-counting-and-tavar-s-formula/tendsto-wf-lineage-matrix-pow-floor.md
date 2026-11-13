# Kingman's theorem for the lineage count

For `t ≥ 0`, the `⌊t M⌋`-generation transition
matrix of the Wright–Fisher ancestral lineage count converges, as the population size `M`
tends to infinity, to the transition matrix `exp (t • G)` of the pure-death process with rates
`k.choose 2`.

## Sources

- Kingman (1982); Durrett (2008), ch. 1. Proves the deferred entry `tendsto_wfLineageMatrix_pow_floor`.
