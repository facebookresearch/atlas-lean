# Bipartite structure of opposition-distance Rips persistence

For a protein-ligand complex, take a set $X = X_P \cup X_L$ of atom centers (protein atoms $X_P$, $|X_P| = n$, and ligand atoms $X_L$, $|X_L| = m$, possibly restricted to given element types) and the **opposition distance**

$$d_{\mathrm{op}}(a, b) = \begin{cases} \|a - b\| & \text{if } a, b \text{ belong to different molecules}, \\ \infty & \text{if } a, b \text{ belong to the same molecule}, \end{cases}$$

which is not a metric (it violates the triangle inequality). Let $\mathrm{VR}^{\varepsilon}$ be the Vietoris-Rips complex of $(X, d_{\mathrm{op}})$ at scale $\varepsilon$.

**Proposition.** Assume $n, m \ge 1$.

1. $\mathrm{VR}^{\varepsilon}$ has no simplices of dimension $\ge 2$; it is the bipartite graph $G_\varepsilon$ with an edge $\{a, b\}$, $a \in X_P$, $b \in X_L$, whenever $\|a - b\| \le \varepsilon$.
2. Every $0$-dimensional bar is born at $0$. The finite death times are the edge lengths of a minimum spanning tree of the complete bipartite graph $K_{n,m}$ weighted by Euclidean distance, and one bar never dies.
3. Every $1$-dimensional bar has infinite death time. Its birth times are the lengths of the $nm - (n + m - 1)$ edges of $K_{n,m}$ outside that spanning tree.

Each diagram is thus encoded by one multiset of scalar **critical values** (deaths in dimension $0$, births in dimension $1$), all of which are protein-ligand interatomic distances. An **internuclear persistence contour** is the function $\gamma(r) = \sum_{c} \exp\big(-(r - c)^2 / (2s^2)\big)$ summing Gaussians of a fixed width $s$ (0.1 Å) centered at the critical values $c$; integrating $\gamma$ over fixed bins gives the discretized contour, and a small set of selected bins across element-type pairs forms the **persistence fingerprint** used to predict binding affinity.

## Expansion

A $2$-simplex would need all three pairwise distances finite, but any three atoms include two from the same molecule, so (1) holds. Adding the edges of $G_\varepsilon$ in increasing length is Kruskal's algorithm: an edge joining two components kills a $0$-class (born at $0$, since all vertices are present at $\varepsilon = 0$), and an edge inside a component creates an independent cycle; without $2$-simplices no cycle is ever filled, giving (2) and (3), and the count in (3) is the cycle rank $nm - (n+m) + 1$ of the connected graph $K_{n,m}$. Hence the two-dimensional persistence diagrams collapse to one-dimensional data, and each fingerprint component is roughly a count of protein-ligand atom pairs of given elements at a given distance, which makes models built on it interpretable.

## Sources

- Y. Long, B. R. Donald, "Predicting Affinity Through Homology (PATH): Interpretable binding affinity prediction with persistent homology", PLoS Computational Biology (2025), Methods (opposition distance, Eq. 2; internuclear persistence contours; persistence fingerprint; Theorem 1) and Results (computational complexity of the persistence fingerprint). <https://doi.org/10.1371/journal.pcbi.1013216> (PMC12226026)
