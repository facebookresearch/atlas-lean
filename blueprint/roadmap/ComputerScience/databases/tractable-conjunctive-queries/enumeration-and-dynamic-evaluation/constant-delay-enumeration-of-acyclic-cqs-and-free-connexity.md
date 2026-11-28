# Constant-delay enumeration of acyclic conjunctive queries is characterized by free-connexity

**Theorem (Bagan, Durand and Grandjean).** Let $Q$ be an acyclic conjunctive query.

1. If $Q$ is [free-connex](free-connex-acyclic-conjunctive-queries.md), then $\mathrm{Enum}\langle Q\rangle$ is in
   $\mathrm{DelayC}_{\mathrm{lin}}$: the answers can be enumerated with constant delay after linear preprocessing.
2. If $Q$ is not free-connex and is self-join free, then $\mathrm{Enum}\langle Q\rangle$ is not in $\mathrm{DelayC}_{\mathrm{lin}}$,
   assuming that the product of two $n \times n$ Boolean matrices cannot be computed in time $O(n^2)$.
Here, as in the sources, every argument of every atom is a variable; queries with constants in atoms are not covered.

## Depends on

- [Enumeration with linear preprocessing and constant delay](enumeration-with-linear-preprocessing-and-constant-delay.md)
- [Free-connex acyclic conjunctive queries](free-connex-acyclic-conjunctive-queries.md)

## Sources

- N. Carmeli and M. Kröll, "Enumeration complexity of conjunctive queries with functional dependencies", *Proceedings of ICDT 2018*; arXiv:1712.07880 <https://arxiv.org/abs/1712.07880>, Theorem 1 in Section 2.
- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Section 1 (related work).
- G. Bagan, A. Durand and E. Grandjean, "On acyclic conjunctive queries and constant delay enumeration", *Proceedings of CSL 2007*, LNCS 4646, pp. 208–222, as credited by the other sources.
