# Maximum convex subcoloring of a taxonomically labelled tree

**Setting.** Let $T$ be a rooted phylogenetic tree and $\chi:F\to C$, $F\subseteq L(T)$, a leaf coloring (e.g. taxonomic labels at a fixed rank). A color is **cut** by an edge if it occurs on both sides; $\tilde\chi(e)$ is the set of colors cut by $e$. The **badness** is $\beta=\max_e|\tilde\chi(e)|$, and $\chi$ is **convex** if $\beta\le1$ (each color occupies a connected region). A subcoloring restricts $\chi$ to $G\subseteq F$; its size is $|G|$. Let $\tau$ be the number of colors cut by some edge with $|\tilde\chi(e)|\ge2$ (the bad colors). The discord between the tree and the taxonomy at that rank is measured by:

**Problem 1.** Find a largest convex subcoloring of $\chi$.

This is equivalent to minimum convex recoloring of the leaves (uncolor exactly the recolored leaves), which is NP-hard; the earlier fixed-parameter algorithm runs in $O(n\,d^3\,\tau\,\mathrm{Bell}(\tau))$ for maximum degree $d$.

**Color allocations.** For an internal node $i$ with children $t(i)$, let $\kappa(i)$ be the colors cut by the edge above $i$. An almost partition of $Y\subseteq C$ is $(b,\pi)$ with $\pi$ a tuple of color sets, $\bigcup_j\pi_j=Y$ and $\bigcup_{j<j'}\pi_j\cap\pi_{j'}\subseteq\{b\}$. A legal allocation at $i$ for a set $X\subseteq\kappa(i)$ entering from above and parent color $c$ is an almost partition of the colors in play $X\cup\big(\bigcup_{j\in t(i)}\kappa(j)\setminus\kappa(i)\big)$ with $\pi_j\subseteq\kappa(t(i)_j)$ and $b=c$ whenever $c\in X$.

**Proposition 1.** Every compatible choice of legal allocations at all internal nodes (an implicit subcoloring) defines a convex subcoloring, and every convex subcoloring arises this way.

**Theorem 1.** Maximizing over implicit subcolorings by recursion on questions $(c,X)$ at each node solves Problem 1 in time

$$O\big(n\,d\,\beta^2\,2^{d+\beta}\,(d-1)^{d\beta/2}\big),$$

which is favourable for nearly bifurcating trees with moderate badness. An admissible upper bound on subtree answers turns the recursion into an exact branch-and-bound (Algorithm 1).

## Expansion

Convexity fails exactly when an edge carries two colors, which the almost-partition condition forbids locally: two child subtrees may share only the node's own color $b$, and that color is forced to propagate along any path where it appears above and below. Only colors cut by nearby edges need to be tracked, and each color in play is cut by at least two edges at the node, so at most $d\beta/2$ colors are in play; enumerating their allocations to the $d-1$ children and the placement of $b$ gives the per-node factor, and there are $O(n)$ nodes.

## Sources

- F. A. Matsen, A. Gallagher, "Reconciling taxonomy and phylogenetic inference: formalism and algorithms for describing discord and inferring taxonomic roots", Algorithms for Molecular Biology 7:8 (2012), Definitions 1–12, Problem 1, Proposition 1, Theorem 1 and Algorithm 1, <https://doi.org/10.1186/1748-7188-7-8>, PMCID: PMC3384453.
