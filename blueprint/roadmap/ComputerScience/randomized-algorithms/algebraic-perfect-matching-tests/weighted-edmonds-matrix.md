# The weighted Edmonds matrix of Mulmuley, Vazirani and Vazirani

For a bipartite graph $G$ on $[n] \times [n]$ and edge weights $w : E(G) \to \mathbb{N}$, the **weighted Edmonds matrix** $B$ is the integer matrix with $B_{ij} = 2^{w(i,j)}$ if $ij \in E(G)$ and $0$ otherwise. The weight of a perfect matching $M$ is $w(M) = \sum_{e \in M} w(e)$, and $w$ is **isolating** if exactly one perfect matching attains the minimum weight.

## Depends on

- [The Edmonds matrix of a bipartite graph](edmonds-matrix.md)
- [Isolation lemma](../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)

## Sources

- K. Mulmuley, U. V. Vazirani and V. V. Vazirani, "Matching is as Easy as Matrix Inversion", Combinatorica 7(1), 1987.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
