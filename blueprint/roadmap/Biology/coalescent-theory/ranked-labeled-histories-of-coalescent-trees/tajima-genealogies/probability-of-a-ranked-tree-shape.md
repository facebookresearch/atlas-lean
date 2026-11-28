# Probability of a ranked tree shape under the coalescent

A *ranked tree shape* on $n$ leaves, also called a Tajima's genealogy without its times, is a rooted binary tree whose leaves are unlabelled and whose $n-1$ internal nodes are labelled $2, \dots, n$ by their order in time, the root being node $2$. A *cherry* is an internal node both of whose children are leaves. Under Kingman's $n$-coalescent the ranked tree shape $F$ with $c$ cherries has probability

$$\Pr(F) = \frac{2^{\,n - c - 1}}{(n-1)!},$$

independently of the effective population size trajectory $N(t)$, because at each coalescence event the pair that merges is chosen uniformly among the available pairs irrespective of $N$. The number of ranked tree shapes on $n$ leaves is the $n$-th Euler zigzag number — $1, 1, 1, 2, 5, 16, 61, 272, 1385, 7936$ for $n = 1, \dots, 10$ — against $n!(n-1)!/2^{\,n-1}$ labelled topologies.

## Depends on

- [Random joining](../random-joining.md)
- [Rate matrix of Kingman's partition-valued coalescent](../../partition-valued-kingman-coalescent/partition-rate.md)
- [The time-changed coalescent as the limit of a Wright–Fisher model of varying size](../../site-frequency-spectrum-under-variable-populatio/derivation-of-the-time-changed-coalescent-from-a.md)

## Proof depends on

- [Every ranked history is equally likely under random joining](../random-joining-singleton-eq-inv.md)

## Expansion

Map each labelled coalescent history to its ranked tree shape by forgetting the leaf labels. Every labelled ranked history has probability $\prod_{k=2}^{n} \binom{k}{2}^{-1}$, which equals $2^{n-1}/(n!\,(n-1)!)$, so $\Pr(F)$ is that value times the number of labelled histories mapping onto $F$. Exactly $n!/2^{c}$ labelled ranked histories map onto $F$ (the $n!$ leaf labellings, the two leaves of each cherry being interchangeable), so $\Pr(F) = \tfrac{n!}{2^c}\cdot\tfrac{2^{n-1}}{n!\,(n-1)!} = \tfrac{2^{n-c-1}}{(n-1)!}$; for $n = 4$ the caterpillar ($c = 1$) and balanced ($c = 2$) shapes receive $12$ and $6$ of the $18$ labelled histories. Equivalently, $F$ has $2^{n-1-c}$ orderings among the $(n-1)!$ equally likely ordered ranked trees, one factor two for each internal node that is not a cherry, whose two child subtrees can be placed in either order; summing $2^{n-1-c}$ over all ranked tree shapes therefore gives $(n-1)!$, whereas the Euler zigzag number counts the shapes themselves. Because the probability does not involve $N(t)$, the ranked tree shape and the vector of coalescence times factor in the law of a Tajima's genealogy, and only the times carry information about past population size.

## Sources

- J. A. Palacios, A. Véber, L. Cappello, Z. Wang, J. Wakeley, S. Ramachandran, "Bayesian estimation of population size changes by sampling Tajima's trees", *Genetics* 213 (2019), 967–986, <https://doi.org/10.1534/genetics.119.302373> (PMC6827370). Materials and Methods, "Tajima's genealogies", Equation (4).
- J. A. Palacios, J. Wakeley, S. Ramachandran, "Bayesian nonparametric inference of population size changes from sequential genealogies", *Genetics* 201 (2015), 281–304, <https://doi.org/10.1534/genetics.115.177980> (PMC4566269). Appendix, Equation (26).
- F. Tajima, "Evolutionary relationship of DNA sequences in finite populations", *Genetics* 105 (1983), 437–460, <https://doi.org/10.1093/genetics/105.2.437>.
