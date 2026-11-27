# Stable triplet covers are minimal strong lassos

Let $T$ be a fully resolved (all interior vertices of degree $3$) $X$-tree with $n = |X| \ge 3$ leaves, and $d_{(T,w)}$ the path metric on $X$ for a proper (positive) edge weighting $w$. A **cord** is a pair $ab$ of distinct leaves; for a set $\mathcal L$ of cords, $(T,w)$ and $(T',w')$ are $\mathcal L$-isometric if their distances agree on every cord of $\mathcal L$. Then $\mathcal L$ is an *edge-weight lasso* for $T$ if $\mathcal L$-isometry of $(T,w)$ and $(T,w')$ forces $w = w'$, a *topological lasso* if $\mathcal L$-isometry of $(T,w)$ and $(T',w')$ forces $T' \cong T$, and a **strong lasso** if both. Every lasso must be a *cover*: for each interior vertex $v$, $\mathcal L$ contains a cord joining each pair of the three components of $T - v$.

Let $\mathrm{clus}(T)$ be the set of clusters (leaf sets on either side of an edge). A map $f:\mathrm{clus}(T)\to X$ is a **stable transversal** if $f(A)\in A$ for all $A$ and $f(A)\in B\subseteq A$ implies $f(B) = f(A)$. For an interior vertex $v$ with component leaf sets $A^1_v, A^2_v, A^3_v$, put

$$\mathcal L_{(T,f)} = \bigcup_{v\ \text{interior}}\big\{f(A^1_v)f(A^2_v),\ f(A^2_v)f(A^3_v),\ f(A^3_v)f(A^1_v)\big\},$$

a **stable triplet cover**. (A general triplet cover is $\mathcal L_{(T,f)}$ with $f$ only transversal; every triplet cover is an edge-weight lasso.)

**Theorem.** If $\mathcal L$ is a stable triplet cover of a fully resolved $X$-tree $T$ with $n \ge 3$, then

1. the graph $(X,\mathcal L)$ is a $2d$-tree: its vertices can be ordered $x_1,\dots,x_n$ with $x_1x_2\in\mathcal L$ and each $x_i$, $i \ge 3$, adjacent to exactly two of $x_1,\dots,x_{i-1}$;
2. $\mathcal L$ is a shellable lasso for $T$, hence a strong lasso;
3. $|\mathcal L| = 2n - 3$, so $\mathcal L$ is a minimal strong lasso.

Moreover, if $\mathcal L$ contains a shellable lasso for $T$ and $d = d_{(T,w)}$, the closure of $\mathcal L$ under the four-point extension rule (whenever all cords of a quartet $\{x,y,u,z\}$ but $xz$ are known and $d(x,y) + d(u,z) < d(x,u) + d(y,z)$, set $d(x,z) = d(x,u) + d(y,z) - d(y,u)$) is all of $\binom X2$, so $T$ and $w$ are reconstructed from $d|_{\mathcal L}$ in polynomial time.

## Depends on

- [Quartet support and determination of trees by quartets](../../quartet-support-and-determination-of-trees-by-qu/README.md)

## Expansion

Induct on $n$ by removing a cherry: if $y$ is a leaf of a cherry $\{x,y\}$ not chosen by $f$ on the larger clusters, then deleting $y$ gives a fully resolved tree $T'$ and the restriction of $f$ is a stable transversal for $\mathrm{clus}(T')$ whose stable triplet cover is $\mathcal L$ minus the two cords at $y$. Stability guarantees that $y$ appears in exactly two cords, which gives the $2d$-tree ordering and the count $|\mathcal L| = |\mathcal L'| + 2$, starting from $3$ cords at $n = 3$. The two cords at $y$ together with the known distances in $T'$ provide, for each missing cord through $y$, a pair of pivots forming a quartet whose other five distances are already known; this is a shellable ordering, and shellable lassos are strong lassos. Minimality holds because a strong lasso on $n$ leaves must determine the $2n-3$ edge weights.

## Sources

- Katharina T. Huber, Mike Steel, "Reconstructing fully-resolved trees from triplet cover distances", arXiv (2012). Section 2 (lassos, shellability, covers, triplet covers), Section 3 (stable transversals), Section 4 ($2d$-trees, Theorem 4.1), Section 5 (extension rule, Theorem 5.1). <https://doi.org/10.48550/arXiv.1209.2391>. Published version: "Tree Reconstruction from Triplet Cover Distances", The Electronic Journal of Combinatorics 21(2) (2014), P2.15, <https://doi.org/10.37236/3388>; locators above refer to the arXiv version.
