# The marginal genealogy at each locus of the ancestral recombination graph is Kingman's

In the [coalescent with recombination on $L$ loci](../two-locus-coalescent/coalescent-with-recombination-ancestral-material.md), fix a locus $x$. The process of partitions of the sample by the lineage ancestral at $x$, read off the path of the graph, is equal in law to Kingman's $n$-coalescent, realized as a continuous-time Markov chain path.

## Depends on

- [Generator-level lumpability of the ancestral recombination graph to one locus](generator-level-lumpability-of-the-arg-to-each-l.md)
- [Coalescent with recombination: ancestral-material state space and generator](../two-locus-coalescent/coalescent-with-recombination-ancestral-material.md)

## Proof depends on

- [Finite-dimensional distributions](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)

## Expansion

1. The equality in law from [the lumpability of the generator](generator-level-lumpability-of-the-arg-to-each-l.md) and the [finite-dimensional distributions](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md) of the two chains.
2. Checks: for $L = 1$ the map is the identity, and for two loci and two samples the pair coalescence time at one locus has mean $1$.

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (marginal trees).
- C. Wiuf and J. Hein, Recombination as a point process along sequences, *Theor. Popul. Biol.* 55 (1999), 248–259, <https://pubmed.ncbi.nlm.nih.gov/10366550/> (local trees along the sequence).
