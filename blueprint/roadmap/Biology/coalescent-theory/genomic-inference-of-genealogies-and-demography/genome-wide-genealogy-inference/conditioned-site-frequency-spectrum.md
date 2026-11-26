# Conditioned site frequency spectrum

Consider a sample of $n$ haploid sequences at a neutral, non-recombining site under the coalescent, in which two of the sequences form a *distinguished* diploid individual and the remaining $n - 2$ are *undistinguished*. Let $T$ be the coalescence time (TMRCA) of the two distinguished lineages, and, at a segregating site under the infinite-sites model, let $a \in \{0, 1, 2\}$ be the number of derived alleles carried by the distinguished individual and $b \in \{0, 1, \dots, n-2\}$ the number carried by the undistinguished haplotypes.

**Definition.** The *conditioned site frequency spectrum* (CSFS) for a time interval $I$ is the joint law of $(a, b)$ given $T \in I$:

$$\mathrm{CSFS}_I(a, b) = \mathbb P\bigl(a, b \mid T \in I\bigr), \qquad (a, b) \in \{0,1,2\} \times \{0, \dots, n-2\}.$$

**Marginal identity.** Since $a + b$ is the derived-allele count in the full sample, averaging the CSFS over the law of $T$ and summing along the anti-diagonals $a + b = j$ recovers the ordinary site frequency spectrum of $n$ haploids:

$$\sum_{I} \mathbb P(T \in I) \sum_{a + b = j} \mathrm{CSFS}_I(a, b) = \mathbb P(\text{derived count} = j), \qquad j = 1, \dots, n - 1,$$

when the intervals $I$ partition $[0, \infty)$.

**Coalescent HMM with CSFS emissions.** Along the genome, the hidden state is the discretized TMRCA $T$ of the distinguished pair, evolving under a sequentially Markov approximation to the coalescent with recombination, exactly as in the pairwise model; the emission at a site is the pair $(a, b)$ with law $\mathrm{CSFS}_I$. With $b$ ignored this reduces to the pairwise sequentially Markov coalescent, whose emission is only whether the individual is heterozygous. Because undistinguished branch lengths remain correlated along the sequence even given $T$, the full CSFS is emitted only at every $k$-th site (thinning), with $k$ growing linearly in $n$.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../../two-locus-coalescent/sequentially-markov-coalescent-smc-smc-pairwise.md)

## Expansion

The marginal identity is the law of total probability: conditioning on $T$ and then forgetting which lineages are distinguished leaves the unconditioned derived count. The CSFS itself is computed from the coalescent by conditioning the genealogy on the time at which the two distinguished lineages meet; the undistinguished lineages then coalesce among themselves and into the distinguished subtree.

## Sources

- J. Terhorst, J. A. Kamm and Y. S. Song, *Robust and scalable inference of population history from hundreds of unphased whole genomes*, Nat. Genet. 49 (2017), 303–309, <https://doi.org/10.1038/ng.3748>, PMCID PMC5470542 (Online Methods: theoretical model, thinning, transition function; derivation of the CSFS in the Supplementary Note).
