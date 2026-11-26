# Fixed-parameter algorithm for the tree-child hybridization number of many trees

Let $\mathcal T=\{T_1,\dots,T_t\}$ be rooted binary phylogenetic trees on a common leaf set $X$, $|X|=n$. The **tree-child hybridization number** $h_{tc}(\mathcal T)$ is the minimum number of reticulations $h(N)=\sum_v\max(0,\deg^-(v)-1)$ over all tree-child networks $N$ on $X$ that display every $T_i$.

**Cherry picking sequences.** $\{x,y\}$ is a *cherry* of a tree if $x$ and $y$ are siblings; it is a cherry of $\mathcal T$ if it is a cherry of some tree, and a *trivial cherry* if it is a cherry of every tree that contains both $x$ and $y$. Applying a pair $(x,y)$ removes $x$ (and suppresses the parent of $y$) in each tree where $\{x,y\}$ is a cherry. A sequence $S=\langle(x_1,y_1),\dots,(x_r,y_r),(x_{r+1},-)\rangle$ is a *tree-child cherry picking sequence* for $\mathcal T$ if it reduces every tree to the single leaf $x_{r+1}$ and $y_j\ne x_i$ for all $i<j$. Its weight is $w(S)=|S|-|X|$. Linz and Semple showed $h_{tc}(\mathcal T)=\min_Sw(S)$, and a tree-child network $N$ displaying $\mathcal T$ with $h(N)\le w(S)$ can be built from $S$ in linear time.

**Theorem.** Given $t$ binary $X$-trees with $|X|=n$ and an integer $k$, one can decide whether $h_{tc}(\mathcal T)\le k$ and, if so, output a tree-child cherry picking sequence of weight at most $k$ and a tree-child network displaying $\mathcal T$ with at most $k$ reticulations, in time

$$O\big((8k)^k\,nt\log t+nt\log(nt)\big).$$

The key structural facts are:

1. (Safe reduction) If $\{x,y\}$ is a trivial cherry of $\mathcal T/S$ and $y$ is not forbidden (not among $x_1,\dots,x_r$), some optimal tree-child extension of $S$ picks $(x,y)$ next.
2. (Kernel for branching) If $\mathcal T/S$ has a solution of weight at most $k$ and no trivial cherries, then $\mathcal T/S$ has at most $4k$ distinct cherries.

## Expansion

The algorithm applies trivial-cherry reductions until none remain. It then branches on every ordered pair $(x,y)$ from the at most $4k$ cherries, giving at most $8k$ children. Each branching step on a non-trivial cherry increases the weight, so the search tree has depth at most $k$ and at most $(8k)^k$ leaves. Each node of the search tree costs $O(nt\log t)$ with suitable cherry bookkeeping. Unlike earlier exact methods, which handled only two trees or bounded $t$, the parameter here is the reticulation number alone; the number of trees enters polynomially. With pruning of dominated pairs and parallel search, instances with up to 100 input trees can be solved on a desktop machine.

## Sources

- Leo van Iersel, Remie Janssen, Mark Jones, Yukihiro Murakami and Norbert Zeh, "A Practical Fixed-Parameter Algorithm for Constructing Tree-Child Networks from Multiple Binary Trees", arXiv:1907.08474 (2019), Section 2 (cherry picking sequences), Theorem 1 and Proposition 2 (after Linz–Semple), Theorem 3, Corollary 4, Propositions 8–9 and 14, <https://doi.org/10.48550/arXiv.1907.08474>.
