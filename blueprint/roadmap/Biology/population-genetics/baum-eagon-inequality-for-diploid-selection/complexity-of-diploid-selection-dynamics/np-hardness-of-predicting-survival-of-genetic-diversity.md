# NP-hardness of predicting the survival of genetic diversity

Let $A$ be the symmetric positive fitness matrix of a single-locus, $n$-allele diploid population evolving under the selection map $x_i' = x_i (A\mathbf{x})_i / \mathbf{x}^{\top}A\mathbf{x}$ on the simplex $\Delta_n$. A fixed point is **mixed** if at least two alleles have positive frequency. Say that **diversity survives** if, with initial frequencies drawn uniformly from $\Delta_n$, the dynamics converges with positive probability to a mixed fixed point.

**Theorem.**

1. Given a symmetric matrix $A$, deciding whether the game $(A,A)$ has a mixed (strict) Nash stable, equivalently linearly stable, strategy is NP-complete; deciding whether the selection map has a mixed (asymptotically) stable fixed point is NP-hard. This remains true when $A$ is strictly positive, or when exactly one row of $A$ has a dominating diagonal ($A_{ii} > A_{ij}$ for all $j \ne i$).
2. Consequently, given a fitness matrix $A$, it is NP-hard to decide whether diversity survives, and it is NP-hard to decide whether a given allele survives.
3. In contrast, if the entries of $A$ are drawn independently and uniformly at random, diversity survives almost surely with probability at least $\tfrac13 - o(1)$.

Item 3 rests on the observation that when every diagonal entry is dominated (each homozygote is less fit than some heterozygote carrying the same allele) every pure fixed point is linearly unstable, so almost every orbit converges to a mixed fixed point; this generalizes Kalmus's heterozygote-advantage condition for two alleles.

## Depends on

- [Stability hierarchy for fixed points of diploid selection](stability-hierarchy-of-fixed-points-of-diploid-selection.md)

## Expansion

The reduction is from $k$-Clique. From a graph $G$ on $n$ vertices one builds a symmetric $2n \times 2n$ matrix whose first block is derived from the adjacency matrix, whose second block has a large diagonal, with coupling $k-1$ between vertex $i$ and its copy $n+i$ and small negative entries elsewhere; then $G$ has a clique of size $k$ iff the game has a mixed strict Nash stable strategy, and the support of such a strategy identifies a clique. Positivity is then restored by adding a constant to every entry, which does not change the sets of Nash stable and strict Nash stable strategies. Because Nash stability equals linear stability and strict Nash stability implies asymptotic stability, the same construction transfers hardness to the dynamics. The random-landscape bound follows by computing the probability that every diagonal entry of an i.i.d. matrix is dominated.

## Sources

- Ruta Mehta, Ioannis Panageas, Georgios Piliouras, Sadra Yazdanbod, "The Complexity of Genetic Diversity", in *24th Annual European Symposium on Algorithms (ESA 2016)*, LIPIcs 57 (2016), 65:1–65:17, <https://doi.org/10.4230/LIPIcs.ESA.2016.65>; preprint arXiv:1411.6322, <https://doi.org/10.48550/arXiv.1411.6322>. Numbering of arXiv v2: Section 6 (Theorems 6.6–6.9), Appendices C–D.
