# Generator-level lumpability of the ancestral recombination graph to one locus

Consider the [coalescent with recombination on $L$ loci](../two-locus-coalescent/coalescent-with-recombination-ancestral-material.md), with generator $Q_{\mathrm{ARG}}$ on its states of ancestral material. For a locus $x$, let $\Pi_x$ map a state to the partition of the sample by the lineage that carries ancestral material at $x$. Then $\Pi_x$ intertwines $Q_{\mathrm{ARG}}$ with [the rate matrix $Q_n$ of Kingman's partition-valued coalescent](partition-rate.md):

$$Q_{\mathrm{ARG}}\, \Pi_x = \Pi_x\, Q_n,$$

with $\Pi_x$ read as the matrix of the map. This is Dynkin's lumpability criterion at the level of generators.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](../two-locus-coalescent/coalescent-with-recombination-ancestral-material.md)
- [Rate matrix of Kingman's partition-valued coalescent](partition-rate.md)

## Expansion

1. Recombination transitions leave $\Pi_x$ unchanged.
2. Coalescence transitions of two lineages both ancestral at $x$ map to the merger of the two blocks at rate $1$. Those of lineages not both ancestral at $x$ leave $\Pi_x$ unchanged.
3. The case $L = 1$ is trivial.

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (marginal trees).
