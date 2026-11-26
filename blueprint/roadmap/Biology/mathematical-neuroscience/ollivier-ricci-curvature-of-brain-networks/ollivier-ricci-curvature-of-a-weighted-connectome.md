# Ollivier–Ricci curvature of a weighted connectome

**Optimal transport.** For probability vectors $p, q$ on a finite metric space $(X, d)$, the $1$-Wasserstein (earth mover's) distance is the value of the linear program

$$W_1(p, q) = \min_{\pi \ge 0} \sum_{i, j} d(x_i, x_j)\, \pi_{ij} \quad \text{s.t.} \quad \sum_j \pi_{ij} = p_i,\ \ \sum_i \pi_{ij} = q_j .$$

**Coarse Ricci curvature.** Let $(X, d)$ be a metric space with a family of probability measures $\{p_x\}_{x \in X}$. The Ollivier–Ricci curvature along $(x, y)$, $x \ne y$, is defined by

$$W_1(p_x, p_y) = \bigl(1 - \kappa(x, y)\bigr)\, d(x, y), \qquad\text{i.e.}\qquad \kappa(x, y) = 1 - \frac{W_1(p_x, p_y)}{d(x, y)} .$$

**On a connectome.** For an undirected graph $G = (V, E, w)$ with symmetric weights $w_{xy} = w_{yx} \ge 0$ ($w_{xy} > 0$ iff $y \in N(x)$), let $d$ be the hop distance, $d_x = \sum_{y \in N(x)} w_{xy}$, and $p_x(y) = w_{xy}/d_x$ (the one-step random-walk law from $x$). The edge curvature is $\kappa(x, y)$ for $\{x, y\} \in E$, and the node curvature is

$$\kappa_x = \sum_{y \in N(x)} \kappa(x, y), \qquad \text{or the weighted version} \qquad \tilde\kappa_x = \sum_{y} p_x(y)\, \kappa(x, y).$$

For adjacent $x, y$, $\kappa(x, y) \le 1$ always, and $\kappa(x, y) \ge -2$ because $W_1(p_x, p_y) \le 3$ when every unit of mass moves from a neighbour of $x$ to a neighbour of $y$.

**Smooth motivation.** On a compact $n$-dimensional Riemannian manifold with normalized uniform measures $m_{r, x}$ on geodesic balls $B_r(x)$, $\mathrm{Ric} \ge k$ if and only if

$$W_1(m_{r,x}, m_{r,y}) \le \Bigl(1 - \frac{k\, r^2}{2(n+2)} + o(r^2)\Bigr) d(x, y)$$

for nearby $x, y$. Moreover (Lott–Sturm–Villani) $\mathrm{Ric} \ge k$ iff the Boltzmann entropy $S(\rho) = -\int \rho \log \rho\, dm$ is $k$-convex along Wasserstein-$2$ geodesics $\rho_t$:

$$S(\rho_t) \ge (1-t) S(\rho_0) + t S(\rho_1) + \tfrac{k}{2}\, t (1 - t)\, W_2(\rho_0, \rho_1)^2, \qquad 0 \le t \le 1 .$$

This is the basis for reading higher curvature as higher entropy and hence greater robustness ($\Delta S \times \Delta \mathrm{Ric} \ge 0$), the heuristic used to rank brain regions.

## Expansion

The graph definition replaces the ball measure by the random-walk step distribution and the geodesic by the hop distance, so $\kappa(x, y)$ compares how cheaply the neighbourhood of $x$ can be moved onto that of $y$ with the distance between the centres. Edges inside densely interconnected clusters (many shared neighbours, triangles) have $W_1 < d$ and positive curvature; bridge edges between modules force mass to travel farther and have negative curvature. The lower bound follows because any neighbour of $x$ is within distance $3$ of any neighbour of $y$ when $x \sim y$, and the upper bound because $W_1 \ge 0$. In diffusion-MRI connectomes, regions with high node curvature are interpreted as robust in the fluctuation-theorem sense, and regions with low curvature as potential points of fragility.

## Sources

- H. Farooq, Y. Chen, T. T. Georgiou, A. Tannenbaum, C. Lenglet, "Network curvature as a hallmark of brain structural connectivity", Nature Communications 10 (2019) 4937, Methods, sections "Wasserstein distance and optimal mass transport", "Curvature and entropy" and "Ollivier–Ricci curvature", Equations (1)–(11), <https://doi.org/10.1038/s41467-019-12915-x> (PMC6821808).
