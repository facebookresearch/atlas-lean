# Polynomial-time tree containment in 3-cuttable networks

Let $U$ be an unrooted binary phylogenetic network on $X$ and $T$ an unrooted binary phylogenetic $X$-tree. $U$ *displays* $T$ if some subgraph of $U$ is a subdivision of $T$ with matching leaf labels. The problem Unrooted Tree Containment asks whether $U$ displays $T$; it is NP-hard for general unrooted networks.

**Theorem.** If $U$ is $q$-cuttable with $q\ge3$ (see [q-cuttable networks and tree-child orientations](q-cuttable-networks-and-tree-child-orientations.md)), then Unrooted Tree Containment for $(T,U)$ can be solved in polynomial time.

Supporting facts used by the algorithm:

- In a $2$-cuttable network every cut-edge induces a split of $X$, and distinct cut-edges induce distinct splits. If $(T,U)$ has a conflicting split, $U$ does not display $T$, and this is decidable in polynomial time.
- For a non-simple $3$-cuttable $U$, branching on a non-trivial cut-edge splits $(T,U)$ into two instances $(T_1,U_1)$ and $(T_2,U_2)$, and $U$ displays $T$ if and only if $U_i$ displays $T_i$ for $i=1,2$.
- In a simple $3$-cuttable network, every image path of a tree edge under an embedding is *entangled*, between any two vertices there is at most one entangled path, and such a path can be found in polynomial time.
- Every $X$-tree with $|X|\ge4$ has a pendant subtree on three leaves containing a cherry, or a pendant subtree on four leaves made of two cherries; reduction rules on these pendant subtrees either reject or produce an equivalent smaller instance.

## Depends on

- [q-cuttable networks and tree-child orientations](q-cuttable-networks-and-tree-child-orientations.md)

## Expansion

The algorithm first removes conflicts detectable from splits, then recursively decomposes along non-trivial cut-edges until each instance is simple. In a simple $3$-cuttable network, uniqueness of entangled paths means that the embedding of a cherry $\{x,y\}$ of $T$ is forced, so a pendant three- or four-leaf subtree of $T$ can be located in $U$ deterministically; the corresponding network edges outside the forced paths are eliminated, which preserves $3$-cuttability and the answer. Each rule shrinks the instance, giving polynomial running time.

## Sources

- L. van Iersel, M. Jones, S. Linz and N. Zeh, "A Class of Unrooted Phylogenetic Networks Inspired by the Properties of Rooted Tree-Child Networks", *Discrete Applied Mathematics* 398 (2027), 76–96, Theorem 11, Observation 12, Lemmas 13-18, Reduction Rules 1-4 with Lemmas 19-23, Lemma 24 and Lemma 25 (correctness and running time of the algorithm), <https://doi.org/10.1016/j.dam.2026.10.022> (preprint arXiv:2603.07000).
