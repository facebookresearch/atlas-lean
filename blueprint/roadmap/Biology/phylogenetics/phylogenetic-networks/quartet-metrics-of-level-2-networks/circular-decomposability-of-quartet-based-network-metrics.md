# Circular decomposability of quartet-based network metrics

**Quartet metric of a tree.** For a quartet tree $Q$ on $\{x,y,z,w\}$ let $\rho_{xy}(Q)=0$ if $x,y$ form a cherry of $Q$ and $1$ otherwise. For a phylogenetic tree $T$ on $X$, $n=|X|\ge4$, and $x\ne y$,

$$d_T(x,y)=\sum_{\{z,w\}\subseteq X\setminus\{x,y\}}2\,\rho_{xy}(T|_{xyzw})+2n-4,\qquad d_T(x,x)=0 .$$

Give each internal edge $e$ of $T$, which splits $X$ into four blocks $X_1,X_2\mid X_3,X_4$ (the two sides of $e$, each divided at the adjacent vertex), the weight $w(e)=|X_1||X_2|+|X_3||X_4|$, and pendant edges the analogous weight. Then $d_T(x,y)$ is the path length from $x$ to $y$ under $w$, every edge weight is at least $n-2$, and $d_T$ is circular decomposable with support exactly the split system $\mathrm{Split}(T)$.

**Displayed quartet metric.** For a semi-directed network $N$ let $\mathcal T(N)$ be its displayed trees, $\mu(T,N)$ the number of ways $N$ displays $T$ and $\mu(N)=\sum_T\mu(T,N)$. Replacing $\rho_{xy}$ by $\tilde\rho_{xy}(N|_{xyzw})$, the average of $\rho_{xy}$ over the quartets displayed by the induced quarnet, defines $\tilde d_N$, and

$$\tilde d_N(x,y)=\frac1{\mu(N)}\sum_{T\in\mathcal T(N)}\mu(T,N)\,d_T(x,y).$$

If $N$ is outer-labeled planar, $\tilde d_N$ is circular decomposable with support $\mathrm{Split}(\mathcal T(N))$, the union of the splits of its displayed trees, which is a circular split system compatible with every circular order induced by $N$.

**NANUQ metric.** Defining $d_N$ the same way from the quarnet values $\rho_{xy}(N|_{xyzw})$ used by NANUQ (from quartet concordance factors), $d_N$ is circular decomposable with support $\mathrm{Split}(\mathcal T(N))$ for every network in $\mathcal B_2$: semi-directed, level-2, outer-labeled planar, galled bloblet networks with at least four leaves.

## Expansion

A metric $d$ is circular decomposable for a circular order $x_0,\dots,x_{n-1}$ iff the split weights $\alpha_{ij}=d(x_i,x_j)+d(x_{i+1},x_{j+1})-d(x_i,x_{j+1})-d(x_{i+1},x_j)$ are nonnegative, and then $d=\sum\alpha_{ij}\delta_{S_{ij}}/2$ over the circular splits. Each $d_T$ is a tree metric with positive weights, hence decomposes on $\mathrm{Split}(T)$. The displayed quartet metric is a convex combination of the $d_T$, and outer-labeled planarity gives a single circular order compatible with every displayed tree, so the combination stays circular decomposable. For NANUQ, $d_N$ differs from the displayed quartet metric by an error term coming from quarnets that are not tree-like; for level-2 bloblets this term is shown blob by blob to keep every $\alpha_{ij}$ nonnegative and to vanish exactly off the displayed splits.

## Sources

- N. Holtgrefe, E. S. Allman, H. Baños, L. van Iersel, "Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances", *Bulletin of Mathematical Biology* 87(12) (2025), 168, Proposition 2.8, Proposition 2.9, Proposition 2.11, Theorem 2.12, Corollary 2.13, Theorem 3.3, Corollary 3.4, Theorem 4.7, <https://doi.org/10.1007/s11538-025-01549-4> (preprint arXiv:2507.17308).
