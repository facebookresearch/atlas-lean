# Counting Dollo-$k$ characters on a tree

**Setting.** For a rooted binary phylogenetic tree $T$ with $n\ge2$ leaves, let $\mathcal D_k(T)$ be the number of binary characters with Dollo score exactly $k$, and $\mathcal P(T)$ the number of persistent characters (Dollo score $0$ or $1$). Let $\mathcal S(T)=\sum_{\ell}\delta_T(\ell)$ be the Sackin index (sum of leaf depths).

**Theorem.**

1. $\mathcal D_0(T)=2n$.
2. (Persistent characters and balance.) $\mathcal P(T)=2\mathcal S(T)-2n+4$, so for persistent characters the count is an affine function of the Sackin index.
3. For $k\ge1$, $\mathcal D_k(T)$ satisfies a recursion over the two root subtrees in terms of the numbers $i_k$ and $e_k$ of independent and extended independent node sets of size $k$ in the subtrees; caching these values gives an $O(k^2|V(T)|)$ algorithm.
4. For $T=(T_a,T_b)$ with $n\ge3$ leaves, $T$ induces Dollo-$(n-2)$ characters if and only if $T$ is a semi-caterpillar tree.
5. For a fully balanced tree $T_h^{\mathrm{fb}}$ of height $h\ge2$, the largest independent node set has size $2^{h-1}$.

Unlike the persistent case, $\mathcal D_k(T)$ for $k\ge2$ is not determined by the Sackin index: trees with equal Sackin index can induce different numbers of Dollo-$k$ characters.

## Depends on

- [Dollo score via the 1-tree](dollo-score-via-the-1-tree.md)

## Expansion

By the 1-tree characterization, a character with score $k$ corresponds to choosing the most recent common ancestor $\mathcal B$ of its state-$1$ leaves together with a set of $k$ maximal $0$-clades below $\mathcal B$, no two in ancestor–descendant relation and none a child of $\mathcal B$. Counting such configurations is a counting problem for independent node sets in rooted subtrees, which splits recursively at each node. For persistent characters ($k\le1$) the count reduces to a sum over leaves of their depths, which is why the Sackin index appears; for $k\ge2$ the independence constraint couples different branches and the count depends on finer tree shape.

## Sources

- Remco Bouckaert, Mareike Fischer, Kristina Wicke, "Combinatorial perspectives on Dollo-$k$ characters in phylogenetics", arXiv:2011.13479 (2020), Theorem 3 (adapted from earlier work on persistent characters), Theorem 4, Corollary 4, Propositions 4–5, <https://doi.org/10.48550/arXiv.2011.13479>.
