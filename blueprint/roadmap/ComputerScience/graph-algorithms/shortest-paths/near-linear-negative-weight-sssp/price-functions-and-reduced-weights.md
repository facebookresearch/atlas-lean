# Price functions, reduced edge weights, and valid reweightings of a directed graph

Let $G=(V,E,w)$ be a directed graph with weights $w:E\to\mathbb{R}$. A *price function* (or *potential*) is any map $\phi:V\to\mathbb{R}$. The *reduced weight* of an edge $(u,v)$ is

$$
w_\phi(u,v)=w(u,v)+\phi(u)-\phi(v),
$$

and $G_\phi=(V,E,w_\phi)$ is the *reweighted graph*; note $(G_\phi)_\psi=G_{\phi+\psi}$. The price function $\phi$ is *feasible* for $G$ if $w_\phi(e)\ge 0$ for all $e\in E$.

Write $E=E^{+}\cup E^{-}$, where $E^{+}=\{e: w(e)\ge 0\}$ and $E^{-}=\{e:w(e)<0\}$. A price function $\phi$ is *valid* if $w_\phi(e)\ge 0$ for every $e\in E^{+}$ (it creates no new negative edge), and $\phi$ *neutralizes* $e\in E^{-}$ if $w_\phi(e)\ge 0$. Two weightings $w,w'$ of the same edge set are *equivalent* (in the sense of Bringmann-Cassis-Fischer) if they have exactly the same shortest paths and assign the same total weight to every cycle; Bernstein-Nanongkai-Wulff-Nilsen use the weaker requirement that the two have the same shortest paths and either both or neither contain a negative cycle, which also allows scaling all weights by a positive constant.

## Sources

- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
- Donald B. Johnson, "Efficient Algorithms for Shortest Paths in Sparse Networks", Journal of the ACM 24(1) (1977).
- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
- Yufan Huang, Peter Jin, Kent Quanrud, "Faster single-source shortest paths with negative real weights via proper hop distance", SODA (2025), arXiv:2407.04872.
