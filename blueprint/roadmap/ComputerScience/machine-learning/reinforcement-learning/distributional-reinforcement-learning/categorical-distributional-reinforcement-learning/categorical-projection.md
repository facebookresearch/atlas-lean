# Categorical projection onto a fixed grid

The categorical projection maps a law on the real line to a law on a fixed finite grid. Each atom's mass is split between the two neighbouring grid points by linear interpolation, and mass outside the grid goes to the nearest endpoint.

Fix a grid $z_1 < z_2 < \dots < z_K$ with $K \ge 2$. For $i = 1, \dots, K$ let $h_i : \mathbb{R} \to [0,1]$ be the hat function

$$h_i(w) = \begin{cases} \dfrac{w - z_{i-1}}{z_i - z_{i-1}} & w \in [z_{i-1}, z_i], \ i > 1, \\ \dfrac{z_{i+1} - w}{z_{i+1} - z_i} & w \in [z_i, z_{i+1}], \ i < K, \\ 1 & w \le z_1 \text{ and } i = 1, \text{ or } w \ge z_K \text{ and } i = K, \\ 0 & \text{otherwise,} \end{cases}$$

where every denominator is positive because the grid is strictly increasing. The categorical projection of a Borel probability measure $\nu$ on $\mathbb{R}$ is

$$\Pi_{\mathcal{C}} \nu = \sum_{i=1}^K \Bigl( \int h_i \, d\nu \Bigr) \delta_{z_i},$$

a probability measure on $\{z_1, \dots, z_K\}$ because $\sum_i h_i \equiv 1$. On [return-distribution functions](../return-distributions-and-policy-evaluation/return-distribution-function.md) $\Pi_{\mathcal{C}}$ acts componentwise; $\mathscr{P}_{\mathcal{C}}$ denotes the probability measures on the grid. For a Dirac mass,

$$\Pi_{\mathcal{C}} \delta_y = \begin{cases} \delta_{z_1} & y \le z_1, \\ \dfrac{z_{i+1} - y}{z_{i+1} - z_i} \delta_{z_i} + \dfrac{y - z_i}{z_{i+1} - z_i} \delta_{z_{i+1}} & z_i < y \le z_{i+1}, \\ \delta_{z_K} & y > z_K, \end{cases}$$

and $\Pi_{\mathcal{C}}$ is affine under mixtures and integrals of measures. Equivalently, its distribution function is

$$F_{\Pi_{\mathcal{C}} \nu}(t) = \begin{cases} 0 & t < z_1, \\ \dfrac{1}{z_{i+1} - z_i} \displaystyle\int_{z_i}^{z_{i+1}} F_\nu(s) \, ds & z_i \le t < z_{i+1}, \ 1 \le i < K, \\ 1 & t \ge z_K. \end{cases}$$

## Depends on

- [Return-distribution function](../return-distributions-and-policy-evaluation/return-distribution-function.md)

## Proof depends on

None.

## Expansion

For $z_i \le t < z_{i+1}$, $F_{\Pi_{\mathcal{C}} \nu}(t) = \sum_{j \le i} \int h_j \, d\nu = \int \bigl( \mathbf{1}_{w \le z_i} + \mathbf{1}_{z_i < w \le z_{i+1}} \frac{z_{i+1} - w}{z_{i+1} - z_i} \bigr) \nu(dw)$. By Fubini this equals the average of $F_\nu$ over $[z_i, z_{i+1}]$, because $\int_{z_i}^{z_{i+1}} \mathbf{1}_{w \le s} \, ds$ is $z_{i+1} - z_i$ for $w \le z_i$, $z_{i+1} - w$ for $z_i < w \le z_{i+1}$, and $0$ beyond. Agreement with the Dirac formula is a direct check, and both sides are affine. Rowland and coauthors define $\Pi_{\mathcal{C}}$ on Dirac masses, extend it affinely to finite mixtures, and give the hat-function and distribution-function forms in their Proposition 6. Bellemare, Dabney and Munos use an equally spaced grid $z_i = V_{\min} + i \, \Delta z$, $0 \le i < N$, with $\Delta z = (V_{\max} - V_{\min})/(N-1)$, which needs $N \ge 2$ and $V_{\min} < V_{\max}$; their eq. (7), clipping $r + \gamma z_j$ to $[V_{\min}, V_{\max}]$ and splitting by hat weights, is this projection of a sampled target. Their Algorithm 1 computes the split with $l = \lfloor b_j \rfloor$ and $u = \lceil b_j \rceil$; when $b_j$ is an integer both weights $u - b_j$ and $b_j - l$ vanish and the atom's mass is lost. Eq. (7) and the definition here do not have that defect. Equal spacing is used by no result of this topic. With $K = 1$ the projection would be the constant $\delta_{z_1}$; that case is excluded.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 3.3, eq. (7), and Appendix A, Proposition 6.
- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 4.1 (the support $\{z_i\}$), Section 4.2, eq. (7), and Algorithm 1.
