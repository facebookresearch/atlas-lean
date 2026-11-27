# Matroid secretary problem

Let $M$ be a matroid on a finite ground set $E$ (a nonempty family of *independent* sets closed under subsets and satisfying the exchange axiom), with nonnegative weights $w : E \to \mathbb{R}$. In the *matroid secretary problem* the elements arrive in uniformly random order; on each arrival the algorithm learns the element's weight and irrevocably accepts or rejects it, keeping the accepted set independent. Its performance is compared with $\mathrm{OPT} = \max\{w(I) : I \text{ independent}\}$. Weights are *well behaved* if distinct elements with equal weight have weight $0$. The classical secretary problem is the rank-one uniform matroid; a *unit-capacity partition matroid* allows at most one element from each block of a partition; the *transversal matroid* of a bipartite graph $G \subseteq L \times R$ has as independent sets the subsets of $L$ that can be matched into $R$.

## Depends on

- [Matching in a bipartite graph](../../graph-algorithms/spanning-trees-flows-matchings/maximum-bipartite-matching/is-matching.md)

## Sources

- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007.
