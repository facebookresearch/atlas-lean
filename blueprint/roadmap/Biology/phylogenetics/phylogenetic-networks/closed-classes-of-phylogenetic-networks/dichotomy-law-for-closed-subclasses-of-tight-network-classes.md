# Dichotomy law for closed subclasses of tight network classes

**Setting.** For a class $\mathcal{N}$ of rooted phylogenetic networks let $\mathcal{N}_n$ be its networks with leaf set contained in $[n]$. For $N$ with leaf set $\mathcal{L}_N$ and $Y \subseteq \mathcal{L}_N$, the restriction $N|Y$ keeps every vertex and edge on a root-to-$Y$ path and suppresses in-degree-1/out-degree-1 vertices and double edges. Every class considered consists of binary networks with leaf sets in $\mathbb N=\{1,2,\dots\}$ and satisfies $(P_1)$: relabelling the leaves of a member by distinct elements of $\mathbb N$ gives a member; and $(P_2)$: for some fixed function $f$, every member with $n$ leaves has at most $f(n)$ vertices. A subset $\mathcal{C} \subseteq \mathcal{N}$ is *closed* if it satisfies $(P_1)$, $(P_2)$ and $(P_3)$: $N \in \mathcal{C}$ and $Y \subseteq \mathcal{L}_N$ imply $N|Y \in \mathcal{C}$. A class is *tight* if every closed subset $\mathcal{C}$ satisfies either $\mathcal{C} = \mathcal{N}$ or

$$\lim_{n\to\infty}\frac{|\mathcal{C}\cap\mathcal{N}_n|}{|\mathcal{N}_n|} = 0 .$$

Trees, galled trees, galled networks, networks with at most $k$ reticulations, networks of height at most $k$ and simplicial networks are closed; tree-child and tree-based networks are not.

**Theorem.**
- The class of phylogenetic trees is tight: every closed set of trees is all trees or asymptotically negligible.
- The classes of tree-child networks and of normal networks are tight. Their largest closed subclasses are, respectively, the galled trees and the phylogenetic trees.
- The class of tree-child networks with at most $k$ reticulations is not tight for any $k \ge 1$.

**Asymptotic constants.** Within galled networks the simplicial galled networks have limiting proportion $e^{-3/8}$; within semi-simplicial networks the simplicial ones have proportion $e^{-1/16}$; within tree-child networks with at most $k$ reticulations the simplicial ones have proportion $2^{-k}$. The number of semi-simplicial networks on $\ell$ labelled leaves satisfies

$$\mathrm{SSN}_\ell \sim \frac{\sqrt{2\sqrt{e\sqrt[4]{e}}}}{4}\,\ell^{-1}\Bigl(\frac{8}{e^2}\Bigr)^{\ell}\ell^{2\ell}, \qquad \ell\to\infty .$$

## Expansion

A closed proper subclass misses some network $N_0$ on $m$ leaves, and closure under restriction then excludes every network that contains $N_0$ as a restriction. For trees and for tree-child or normal networks, a uniformly random large member contains every fixed small pattern on some leaf subset with probability tending to one, so excluding one pattern removes almost everything. The largest closed subclass consists of the members all of whose leaf restrictions stay in the class; for tree-child networks these are exactly the galled trees, and for normal networks only the trees. For tree-child networks with at most one reticulation, the simplicial ones form a closed subclass of limiting proportion $1/2$, so the class is not tight; for $k\ge2$ the simplicial tree-child networks with at most $k$ reticulations have limiting proportion $2^{-k}$ but are not closed, and non-tightness is proved differently from the asymptotic counts of tree-child networks with exactly $k$ reticulations (Proposition 4.6, Remark 4.7).

## Sources

- M. Fuchs, M. Steel, "A dichotomy law for certain classes of phylogenetic networks", *Bulletin of Mathematical Biology* 87(11) (2025), 153, Section 1 definitions, Proposition 2.1, Propositions 3.1-3.2, Theorem 3.3, Theorem 4.1, Lemmas 4.2 and 4.4, Theorem 4.5, Proposition 4.6 and Remark 4.7, <https://doi.org/10.1007/s11538-025-01536-9> (preprint arXiv:2506.23223).
