# Hybridization number of two trees in $O^*(2^n)$ time

Let $X$ be a finite set of taxa with $|X| = n$. A *rooted phylogenetic $X$-tree* is a rooted tree with no vertex of indegree $1$ and outdegree $1$, a root of outdegree at least $2$, and leaves bijectively labelled by $X$; it need not be binary. A *rooted phylogenetic network* on $X$ is a directed acyclic graph with leaves bijectively labelled by $X$ and no vertex of indegree $1$ and outdegree $1$. A tree $T$ is *displayed* by a network $N$ if $T$ can be obtained from a subgraph of $N$ by contracting edges. The *reticulation number* of a network $N$ with vertex set $V$ is

$$ r(N) = \sum_{v \in V:\ d^-(v) \ge 2} \big(d^-(v) - 1\big), $$

and the *hybridization number* $h(T_1, T_2)$ of two rooted phylogenetic $X$-trees is the minimum of $r(N)$ over all networks $N$ displaying both $T_1$ and $T_2$.

**Theorem.** For any two (not necessarily binary) rooted phylogenetic $X$-trees $T_1, T_2$ with $|X| = n$, the hybridization number $h(T_1, T_2)$ can be computed in time $O^*(2^n) = O(2^n \cdot \mathrm{poly}(n))$. Consequently a maximum acyclic agreement forest of $T_1$ and $T_2$ can be computed within the same time bound.

**Recursion.** Let $\mathcal C = \mathrm{Cl}(T_1) \cup \mathrm{Cl}(T_2)$ be the union of the clusters (leaf sets below edges) of the two trees. A subset $S \subseteq X$ is an *ST-set* of $\mathcal C$ if $S$ is compatible with every cluster of $\mathcal C$ and the restricted clusters $\mathcal C|S = \{C \cap S : C \in \mathcal C\}$ are pairwise compatible; non-empty ST-sets correspond to common pendant subtrees of $T_1$ and $T_2$. Writing $ST(\mathcal C)$ for the set of maximal ST-sets (at most $n$ of them, partitioning $X$, computable in polynomial time) and $r(\mathcal C)$ for the minimum reticulation number of a network representing all clusters of $\mathcal C$, one has $r(\mathcal C) = h(T_1, T_2)$, $r(\mathcal C) = 0$ when $\mathcal C$ is compatible, and otherwise

$$ r(\mathcal C) = \min_{S \in ST(\mathcal C)} \big( 1 + r(\mathcal C \setminus S) \big), \qquad \mathcal C \setminus S = \{ C \setminus S : C \in \mathcal C \}. $$

## Expansion

The minimum reticulation number of a cluster set equals the minimum length of an *ST-set tree sequence*: a sequence $S_1, \dots, S_k$ in which each $S_i$ is an ST-set of $\mathcal C_{i-1} = \mathcal C_{i-2} \setminus S_{i-1}$ (with $\mathcal C_0 = \mathcal C$) and the final cluster set $\mathcal C_k$ is compatible. One may restrict to sequences of *maximal* ST-sets, which gives the displayed recursion. Every subproblem reached by the recursion is $\mathcal C | X'$ for some subset $X' \subseteq X$ of surviving taxa, so tabulating $r(\mathcal C | X')$ over all $2^n$ subsets in order of increasing size, each entry consulting at most $n$ smaller entries, gives the $O(2^n \cdot \mathrm{poly}(n))$ bound (with exponential space for the lookup table). Polynomial-time transformations between optimal networks for $r(\mathcal C)$ and optimal hybridization networks, and between these and maximum acyclic agreement forests, transfer the bound. Unlike earlier $O^*(3.18^n)$ and $O^*(3^n)$ bounds, the argument is not restricted to binary trees. Whether $O^*(c^n)$ is possible for some $c < 2$ is left open.

## Sources

- Leo van Iersel, Steven Kelk, Nela Lekić, Leen Stougie, "A short note on exponential-time algorithms for hybridization number", arXiv:1312.1255 (2013), Section 1 (definitions) and Section 2, Theorem 1 with its proof and Equation (1). <https://doi.org/10.48550/arXiv.1312.1255>
