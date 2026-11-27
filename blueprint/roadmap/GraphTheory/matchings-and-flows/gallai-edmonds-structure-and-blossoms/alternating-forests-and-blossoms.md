# Alternating forests, flowers and blossoms of a matching

Let $M$ be a matching of a finite simple graph $G$. An *$M$-alternating forest* is a subforest $F$ of $G$ whose trees are rooted at distinct vertices missed by $M$, each tree containing exactly one missed vertex, such that every root-to-vertex path of $F$ is $M$-alternating with first edge outside $M$, and every edge of $M$ meeting $V(F)$ lies in $F$. Vertices at even (odd) distance from their root are *outer* (*inner*). A *blossom* of $M$ is an odd cycle $B$ of length $2r + 1$ containing exactly $r$ edges of $M$; the unique vertex $b$ of $B$ not covered by $M \cap E(B)$ is its *base*. A *flower* is a blossom $B$ together with an even-length $M$-alternating path $P$, its *stem*, from a missed vertex to $b$ (possibly of length $0$) that meets the blossom only at its base: $V(P) \cap V(B) = \{b\}$. The *contraction* $G / B$ replaces $V(B)$ by one new vertex $\beta$ adjacent to every vertex outside $B$ with a neighbour in $B$, and $M / B = M \setminus E(B)$ is a matching of $G / B$.

## Depends on

- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)
- [Odd components and the Tutte deficiency of a vertex set](odd-components-and-tutte-deficiency.md)

## Sources

- J. Edmonds, "Paths, trees, and flowers", Canadian Journal of Mathematics 17 (1965).
- L. Lovasz, M. D. Plummer, "Matching Theory", Annals of Discrete Mathematics 29, North-Holland (1986).
