# Inconsistency of fully partitioned maximum likelihood under the multispecies coalescent

In the MSC+CFN model, gene trees are drawn independently from the multispecies coalescent on a rooted species tree with topology, branch lengths (in coalescent units) and branch-specific mutation rates, and each locus evolves $L$ binary sites down its gene tree under the Cavender–Farris–Neyman (CFN) two-state symmetric substitution model. *Fully partitioned maximum likelihood* estimates a single tree topology $T$ from $m$ loci by maximizing

$$
\ell^*(T, \Lambda_1, \dots, \Lambda_m) = \sum_{j=1}^m \sum_{i=1}^L \log \mathcal{L}(T, \Lambda_j, \chi_{ij}) ,
$$

where each locus $j$ has its own branch lengths $\Lambda_j$ and $\chi_{ij}$ is site $i$ of locus $j$.

**Theorem.** Fully partitioned maximum likelihood on loci with a bounded number of sites is not statistically consistent and is even positively misleading: for every locus length $L \in \mathbb{N}$ there is a species tree (topology, branch lengths and mutation rates) such that, for data generated under MSC+CFN, as the number of loci $m \to \infty$ the maximum likelihood topology is unique and differs from the true species tree topology with probability tending to $1$.

## Expansion

The counterexample is a four-taxon Felsenstein-zone configuration: two long pendant branches separated by a short internal branch. With only $L$ sites per locus and free branch lengths per locus, each locus contributes a likelihood that favours grouping the long branches, and this bias does not average out as $m \to \infty$ because the per-locus information stays bounded; the law of large numbers then fixes the wrong topology. Increasing the number of loci cannot compensate for short loci: concatenation-style analyses with locus-specific parameters inherit long-branch attraction.

## Sources

- Sebastien Roch, Michael Nute and Tandy Warnow, *Long-branch attraction in species tree estimation: inconsistency of partitioned likelihood and topology-based summary methods*, arXiv:1803.02800, Theorem 1. <https://doi.org/10.48550/arXiv.1803.02800> Published version: Systematic Biology 68 (2018) 281–297, <https://doi.org/10.1093/sysbio/syy061>.
