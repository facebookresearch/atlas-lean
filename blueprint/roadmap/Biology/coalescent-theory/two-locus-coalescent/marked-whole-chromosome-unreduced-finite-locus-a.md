# The unreduced finite-locus ARG and the reduction map

Let the loci carry breakpoint rates $\rho_i \ge 0$ with $\rho = \sum_i \rho_i$. A marked state is a finite set of whole-chromosome lineages, each with a mark of ancestral material at every locus (possibly empty) and marks recording the events of its history. Each lineage recombines at total rate $\rho/2$, at breakpoint $i$ with probability $\rho_i/\rho$, and each pair of lineages coalesces at rate $1$.

1. The process exists as the [minimal continuous-time Markov chain on a countable state space](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/minimal-ctmc-on-a-countable-state-space.md). It does not explode, by domination, and its number of lineages is exactly [the ancestral line count with recombination](lineage-count-birth-death-chain-rho-0-positive-r.md), positive recurrent for $\rho > 0$ and absorbed at $1$ for $\rho = 0$.
2. The reduction map deletes the material at loci that have reached their most recent common ancestor and then the lineages left with no material. Applied pathwise, it gives the reduced [coalescent with recombination](coalescent-with-recombination-ancestral-material.md). It uses the marks, not only the number of lineages.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](coalescent-with-recombination-ancestral-material.md)
- [Minimal CTMC on a countable state space](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/minimal-ctmc-on-a-countable-state-space.md)
- [The ancestral line count with recombination is positive recurrent](lineage-count-birth-death-chain-rho-0-positive-r.md)

## Expansion

1. The construction and nonexplosion, and the projection to the line count.
2. The pathwise reduction and the equality in law with the reduced process.
3. Checks: for $n = 2$ and $L = 2$ there are two marked histories with the same path of the line count but different reduced states, so the count alone does not determine the reduction. For $\rho = 0$ the time of the grand most recent common ancestor equals that of the most recent common ancestor, and the chain is absorbed at one lineage. For $n = 2$ the reduction of the marked path reproduces [the two-locus rate matrix](two-locus-rate.md).

## Sources

- R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer (1997), 257–270, <https://research.monash.edu/en/publications/an-ancestral-recombination-graph/> (the ancestral recombination graph and the grand most recent common ancestor).
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), <https://doi.org/10.1007/978-0-387-78168-6>, Chapter 3.
