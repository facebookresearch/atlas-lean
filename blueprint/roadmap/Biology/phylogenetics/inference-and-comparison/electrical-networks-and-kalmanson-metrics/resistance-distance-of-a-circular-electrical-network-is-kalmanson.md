# Resistance distance of a circular electrical network is Kalmanson

**Setting.** An electrical network $\mathcal{E}$ is a connected graph $\Gamma$ with positive edge conductances $\omega$ and a set of boundary nodes; it is *circular* if $\Gamma$ is embedded in a disk with the $n$ nodes on the boundary circle in order $1,\dots,n$. The effective resistance between nodes $i,j$ is, by Kirchhoff's formula,

$$R_{ij} = \frac{T(\Gamma/ij;\omega)}{T(\Gamma;\omega)},$$

with $T(\cdot;\omega)$ the weighted spanning-tree polynomial and $\Gamma/ij$ the graph with $i,j$ glued. The inverse of the reduced response matrix is the Farris transform (Gromov product) of $R$: $(M_R')^{-1}_{ij} = \tfrac12(R_{in} + R_{jn} - R_{ij})$ for $i \ne j$ and $R_{in}$ on the diagonal.

**Theorem.** $R$ is a metric on the nodes. If $\mathcal{E}$ is a connected circular network, then for any four nodes $i_1,i_2,i_3,i_4$ in circular order the Kalmanson inequalities hold:

$$R_{i_1i_3} + R_{i_2i_4} \ge R_{i_2i_3} + R_{i_1i_4}, \qquad R_{i_1i_3} + R_{i_2i_4} \ge R_{i_1i_2} + R_{i_3i_4}.$$

Consequently $R$ is a circular split metric: $R = \sum_{i<j}\omega_{ij}D_{S_{ij}}$ over the circular splits $S_{ij}$ (contiguous arcs), with non-negative weights

$$\omega_{ij} = \tfrac12\bigl(R_{i,j} + R_{i+1,j+1} - R_{i,j+1} - R_{i+1,j}\bigr),$$

and these weights are, up to sign, the response-matrix entries of the dual network $\mathcal{E}^*$.

**Characterization.** A Kalmanson metric $D$ is the resistance metric of a connected circular electrical network iff the associated matrix $M(D)$ has rank $n-1$ and all its circular $k\times k$ minors, multiplied by $(-1)^k$, are non-negative; equivalently iff $D$ defines a point of the totally non-negative Grassmannian $\mathrm{Gr}_{\ge 0}(n-1,2n)$ with a non-vanishing Plücker coordinate $\Delta_{24\dots 2n-2}$.

## Expansion

Kalmanson's condition is exactly the four-point condition for a metric that is a non-negative combination of circular split pseudometrics (Bandelt-Dress), so it identifies the class of distances a split network drawn on a circle can represent. For a planar network, the Kalmanson differences are minors of the response matrix, which are non-negative by Curtis-Ingerman-Morrow circular planarity. This places NeighborNet-type outputs inside the space of circular electrical networks, whose combinatorics (strand permutations, star-triangle moves, Lam's Grassmannian embedding) supply a reconstruction theory: equivalent minimal circular networks share their response matrix and differ only by star-triangle transformations.

## Sources

- V. Gorbounov, A. Kazakov, "Electrical networks and data analysis in phylogenetics", *Data Analytics and Topology* 1(1) (2025), 33–45, Theorem 3.2, Proposition 3.4, Theorems 3.6, 3.9, 3.14, 3.16, 3.19-3.20 and 4.8, <https://doi.org/10.4310/daat.250513011206> (preprint arXiv:2501.01383).
