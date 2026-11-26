# Tropical supertrees via parametric Fermat–Weber medians

**Setting.** Let $\mathcal{T} = \{T_1,\dots,T_m\}$ be equidistant (ultrametric) rooted metric trees of common height on leaf sets $\mathcal{L}(T_\ell)$, and let $\mathcal{L} = \bigcup_\ell \mathcal{L}(T_\ell)$, $n = |\mathcal{L}|$. For a large parameter $M$ ("big-$M$"), extend each tree to an ultrametric on all of $\mathcal{L}$:

$$D^{(\ell)}_{ij}(M) = \begin{cases} \text{distance in } T_\ell & \text{if } i, j \in \mathcal{L}(T_\ell),\\ M & \text{otherwise.}\end{cases}$$

View the $D^{(\ell)}(M)$ as points of the tropical projective torus $\mathbb{R}^{\binom{\mathcal{L}}{2}}/\mathbb{R}\mathbf{1}$ with the tropical (generalised Hilbert projective) metric $d(x,y) = \max_k (x_k - y_k) - \min_k (x_k - y_k)$. The **Fermat–Weber set** $\mathrm{FW}$ is the set of minimisers of $z \mapsto \sum_\ell d(z, D^{(\ell)}(M))$. It is a bounded polytrope equal to the central cell of the covector decomposition of the points, contained in their tropical convex hull and hence in the (tropically convex) space $\mathfrak{T}(\mathcal{L})$ of equidistant trees. The **tropical median** is the ordinary average of the tropical vertices of $\mathrm{FW}$, and the **tropical supertree** $c(M)$ is the tropical median of the $D^{(\ell)}(M)$.

**Theorem (parametric Fermat–Weber).** For an affine family of $m$ points in $\mathbb{R}^n/\mathbb{R}\mathbf{1}$, written as a matrix $V(M) = U + M\,W \in \mathbb{R}^{m\times n}$ with integral $W \in \mathbb{Z}^{m \times n}$, for every

$$M > \binom{m+n-2}{m-1}\,\|U\|_1$$

the combinatorial type of the covector decomposition of $V(M)$ is constant, and the tropical vertices of $\mathrm{FW}(V(M))$ and the tropical median are affine functions $p + M q$ of $M$.

**Theorem (tropical supertrees).**
1. Any two points in the relative interior of an ordinarily convex subset of $\mathfrak{T}(\mathcal{L})$ are equidistant trees with the same topology.
2. The tropical supertree $c(M)$ has the same tree topology for all $M \gg 0$, and each of its edge lengths depends affinely on $M$ for $M \gg 0$.
3. If $m \ge \binom{n}{2}$, the tropical supertree of $m$ trees on $n$ combined taxa can be computed in $O(n^4 m \log^2 m)$ time.
4. The method is Pareto on nestings: if taxon sets $X, Y$ satisfy $X < Y$ (the lowest common ancestor of $X$ is a strict descendant of that of $X \cup Y$) in every input tree, then $X < Y$ in the supertree.

## Expansion

Missing taxon pairs are pushed to distance $M$, so for large $M$ only the order of $M$-terms matters and the Fermat–Weber problem becomes a parametric linear program whose optimal basis stabilises; vertices then move along rays $p + Mq$. Since $\mathrm{FW}$ is convex in the ordinary sense and its relative interior has constant topology, the median lies in a cell of fixed topology for all large $M$, which defines a canonical supertree independent of the choice of $M$. The explicit bound on $M$ comes from bounding determinants of the relevant constraint matrices.

## Sources

- Andrei Comăneci and Michael Joswig, "Parametric Fermat-Weber and tropical supertrees", arXiv:2211.06328 (2022), Theorem 1, Proposition 2, Theorem 5, Proposition 6, Theorem 7, Corollary 8 and Proposition 9, <https://doi.org/10.48550/arXiv.2211.06328>.
