# Sharp lower bound on the number of trees displayed by a tree-child network

Let $\mathcal N$ be a rooted binary phylogenetic network on a leaf set $X$ with $|X|=n$: a rooted acyclic digraph without parallel arcs whose root has out-degree 2, whose out-degree-0 vertices are $X$, and whose other vertices are tree vertices (in-degree 1, out-degree 2) or reticulations (in-degree 2, out-degree 1). $\mathcal N$ is **tree-child** if every non-leaf vertex has a child that is a tree vertex or leaf; then it has $k\le n-1$ reticulations. A phylogenetic $X$-tree $T$ is **displayed** by $\mathcal N$ if it is obtained by deleting one incoming arc at each reticulation and suppressing degree-2 vertices; $T(\mathcal N)$ is the set of displayed trees up to isomorphism. $\mathcal N$ has an **underlying 3-cycle** if its underlying undirected graph has a cycle of length 3. A normal network (tree-child without shortcuts) with $k$ reticulations displays exactly $2^k$ trees; tree-child networks can display fewer, because different arc deletions can yield the same tree.

**Theorem.** Let $\mathcal N$ be a rooted binary tree-child network with $n$ leaves, $0\le k\le n-1$ reticulations and no underlying 3-cycles. Then $|T(\mathcal N)|=1$ if $k=0$, $|T(\mathcal N)|=2$ if $k=1$, and for $k\ge2$

$$|T(\mathcal N)|\ \ge\ t(n,k)=\begin{cases}2^{k/2}, & k\text{ even},\\[2pt] \dfrac{3}{2\sqrt2}\,2^{k/2}, & k\text{ odd}.\end{cases}$$

The bounds are sharp: for $k\ge2$, equality holds if and only if $\mathcal N$ is an **octopus**, meaning that every non-trivial 2-connected component is the core of a 2-tight caterpillar ladder (a two-reticulation gadget displaying only 2 trees) when $k$ is even, and exactly one non-trivial 2-connected component is the core of a 3-tight caterpillar ladder (three reticulations, 3 trees) with all others 2-tight when $k$ is odd.

## Expansion

The bound function satisfies $t(n,k)=2\,t(n,k-2)$ for $k\ge4$ and $t(n,k)=t(n,k-1)+t(n,k-3)$ for odd $k\ge3$, so an octopus attains it multiplicatively: independent 2-connected components multiply their tree counts, giving $2^{k/2}$ from $k/2$ ladders with 2 trees each, or $3\cdot2^{(k-3)/2}$ with one 3-tree ladder. The proof is by induction on $k$. Deleting a reticulation arc whose tail is closest to the root keeps the network tree-child without 3-cycles, and every displayed tree of $\mathcal N$ is displayed by one of the two networks obtained by deleting either arc into a reticulation; if some reticulation is normal (neither incoming arc a shortcut), the induction hypothesis gives the strict inequality $|T(\mathcal N)|>t(n,k)$ (Lemma 3.5), so extremal networks have no normal reticulation. The base cases $k=2,3$ are handled by characterizing non-essential arcs as the first or last rungs of 2- or 3-tight caterpillar ladders, which identifies the extremal octopus structures.

## Sources

- C. Semple, K. Wicke, "A sharp lower bound for the number of phylogenetic trees displayed by a tree-child network", *Annals of Combinatorics* (2026), Theorem 1.1, Lemmas 2.1-2.2, Lemmas 3.1-3.5 and Lemma 4.1, <https://doi.org/10.1007/s00026-026-00825-x> (preprint arXiv:2508.13414).
