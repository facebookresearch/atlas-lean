# Leaf-reconstructibility of trees, decomposable and low-level networks

**Setting.** An (unrooted) phylogenetic network on a finite set $X$ is a connected graph whose leaves are bijectively labelled by $X$ and such that contracting every *blob* (biconnected component with at least two edges) to a vertex yields a phylogenetic tree on $X$ (no degree-$2$ vertices). It is *binary* if all vertices have degree $1$ or $3$, *decomposable* if it has a cut-edge neither of whose endpoints is a leaf, and *level-$k$* if every biconnected component has reticulation number $|E|-|V|+1\le k$. For a leaf $x$, $N_x$ is obtained by deleting $x$ and its incident edge and suppressing degree-$2$ vertices. The *$X$-deck* of $N$ is the multiset $\{N_x : x\in X\}$, taken up to isomorphisms fixing labels. $N$ is *leaf-reconstructible* if every network $N'$ on $X$ with the same number of vertices and $N'_x\cong N_x$ for all $x\in X$ is isomorphic to $N$. The *leaf-reconstruction number* is the least size of a set $U\subseteq X$ such that agreement of $N'_u$ with $N_u$ for all $u\in U$ already forces $N'\cong N$.

**Theorem.**

1. The numbers of edges and vertices, the reticulation number and the level of a binary network are determined by its $X$-deck.
2. Every phylogenetic tree with at least five leaves is leaf-reconstructible; its leaf-reconstruction number is $2$, unless it is a star, in which case it is $3$. Binary trees with four leaves are not leaf-reconstructible.
3. Every decomposable phylogenetic network with at least five leaves is leaf-reconstructible, with leaf-reconstruction number at most $2$.
4. Every simple binary level-$k$ network with $k\ge 2$ and at least $6k-5$ leaves is leaf-reconstructible; more generally a binary network $N=(V,E)$ on $X$ with $|X|\ge \max\{6(|E|-|V|)+1,5\}$ is leaf-reconstructible. The source's Corollary 4 prints $\min$ here; this page uses $\max$ because the source's proof needs both bounds (Theorem 2 and Lemma 1 need at least five leaves, Corollary 3 needs at least $6k-5$ leaves), and with $\min$ the clause would make 4-leaf binary trees leaf-reconstructible, contradicting item 2. For fixed $k$, almost all binary level-$k$ networks are leaf-reconstructible.
5. Every binary level-$4$ network with at least five leaves has leaf-reconstruction number at most $2$.

## Expansion

For trees, a nontrivial split $A|B$ of $T$ with $a_1,a_2\in A$ survives in $T_{a_1}$ and $T_{a_2}$; a tree $T'$ with the same deck but without $A|B$ would have to contain the two incompatible splits $A\setminus\{a_i\}\mid B\cup\{a_i\}$, a contradiction. Decomposable networks reduce to trees because deleting a leaf commutes with contracting blobs, so the tree of blobs is itself leaf-reconstructible and each blob is recovered from a deck element in which it is untouched. For simple networks, many leaves force a chain of three leaves on one edge of the underlying cubic generator, and the leaf can be put back uniquely. The level-$4$ case is an inspection of generators using local lemmas on cycles, multi-edges and triangles of the generator. Leaf-reconstructibility differs from the classical end-vertex reconstruction problem for graphs because leaves are labelled.

## Sources

- L. van Iersel and V. Moulton, *Leaf-reconstructibility of phylogenetic networks*, arXiv:1701.08982 (2017). <https://doi.org/10.48550/arXiv.1701.08982> Proposition 1 (Section 3), Theorems 1 and 2 (Section 4), Corollaries 3–5 (Section 5), Theorem 3 and Corollary 6 (Section 6), Theorem 4 (Section 7). Published version: SIAM Journal on Discrete Mathematics 32 (2018) 2047–2066, <https://doi.org/10.1137/17m1111930>.
