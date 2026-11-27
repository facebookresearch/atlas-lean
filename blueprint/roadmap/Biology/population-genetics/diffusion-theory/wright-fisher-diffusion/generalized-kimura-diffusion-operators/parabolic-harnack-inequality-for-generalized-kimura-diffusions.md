# Parabolic Harnack inequality for generalized Kimura diffusions

A **generalized Kimura diffusion operator** $L$ on a compact manifold with corners $P$ is a degenerate elliptic operator that, in adapted local coordinates $(x;y) \in S_{n,m} = \mathbb R_+^n \times \mathbb R^m$ near a corner of codimension $n$, has the form

$$Lu = \sum_{i=1}^{n} \big[ x_i \partial_{x_i}^2 + b_i(x;y)\partial_{x_i} \big] u + \sum_{i,j=1}^{n} x_i x_j a_{ij}(x;y) \partial_{x_i}\partial_{x_j} u + \sum_{i=1}^{n}\sum_{l=1}^{m} x_i c_{il} \partial_{x_i}\partial_{y_l} u + \sum_{k,l=1}^{m} d_{kl}(x;y) \partial_{y_k}\partial_{y_l} u + \sum_{l=1}^{m} d_l(x;y) \partial_{y_l} u.$$

The Wright–Fisher generator on the simplex, $\sum_{i,j}(x_i\delta_{ij} - x_i x_j)\partial_{x_i}\partial_{x_j} + \sum_i b_i(x)\partial_{x_i}$ with an inward-pointing drift, is the basic example. The **weights** are the normalized coefficients of the transverse drift on the boundary hypersurfaces $\{x_i = 0\}$, essentially $b_i$ restricted there; biologically they are scaled mutation rates. The weights define the measure

$$d\mu(x;y) = e^{U(x;y)}\, x_1^{b_1(x;y)-1} \cdots x_n^{b_n(x;y)-1}\, dx\, dy$$

with $U$ bounded, and the principal symbol gives the quadratic form $\langle A\nabla u, \nabla v\rangle$. Together they define the Dirichlet form $Q(u,v) = \int \langle A \nabla u, \nabla v\rangle\, d\mu$ and its operator $L_Q$. The intrinsic metric $\rho_i$ is the distance dual to the principal symbol; in the variables $\sqrt{x_i}$ it is uniformly equivalent to the Euclidean distance, and $B^i_r$ denotes an intrinsic ball.

**Metric-measure properties (Epstein–Mazzeo, Proposition 3.1 and Theorem 3.1).** If the weights $b_i$ are positive, satisfy a mild regularity condition and are constant outside a compact set, then $\mu$ is **doubling** for intrinsic balls, $\mu(B_{2r}) \le 2^D \mu(B_r)$ for a constant $D$ and all centers and radii, and a scale-invariant **Poincaré inequality** holds:

$$\int_{B^i_r} |u - u_{B^i_r}|^2\, d\mu \le C r^2 \int_{B^i_r} \langle A\nabla u, \nabla u\rangle\, d\mu.$$

The measure is not Ahlfors regular: $\mu(B_r)$ scales with different powers of $r$ at different boundary strata.

**Theorem (Harnack inequality; Epstein–Mazzeo, Theorem 4.1).** Suppose the $b_i$ are continuously differentiable functions of $(x;y)$, bounded below by a positive constant and constant outside a compact set, $X$ is a continuous compactly supported vector field satisfying the paper's integrability bound near the boundary, and $c$ is bounded, measurable and compactly supported. Let $V_X$ be the first-order term defined by $X$. There is a constant $C$ such that for every $r > 0$, every center $(x;y)$ and every non-negative weak solution of $\partial_t u = (L_Q - V_X - c)u$ in $W = (t-4r^2, t) \times B^i_{2r}(x;y)$,

$$\sup_{W^-} u \le C \inf_{W^+} u, \qquad W^+ = (t-r^2,t)\times B^i_r(x;y), \quad W^- = (t-3r^2, t-2r^2)\times B^i_r(x;y).$$

**Corollary (Hölder continuity; Epstein–Mazzeo, Corollary 4.1).** With $c = 0$, there are $\gamma > 0$ and $C$ such that every weak solution of $\partial_t u = (L_Q - V_X)u$ in $W$ satisfies, for $(s_j, x_j;y_j) \in (t-r^2,t)\times B^i_r(x;y)$,

$$|u(s_1,x_1;y_1) - u(s_2,x_2;y_2)| \le C \sup_W |u| \left( \frac{|s_1 - s_2|^{1/2} + \rho_i((x_1;y_1),(x_2;y_2))}{r} \right)^{\gamma}.$$

## Depends on

- [Backward generator of the Wright–Fisher diffusion with selection](../generator.md)

## Expansion

The proof follows Moser's iteration in the form developed by Grigor'yan, Saloff-Coste and Sturm for Dirichlet spaces: volume doubling plus a scale-invariant Poincaré inequality for intrinsic balls imply a local Sobolev inequality, which drives mean-value estimates for sub- and supersolutions and, through the Bombieri–Giusti lemma, the Harnack inequality. The main work is the Poincaré inequality near corners, where the weighted measure $x_i^{b_i - 1}dx_i$ is handled by one-dimensional weighted inequalities with constants uniform for weights in a compact subset of $(0,\infty)$, and the singular lower-order terms produced by variable weights are absorbed by a small multiple of the Dirichlet form. Positivity of the weights is essential: along boundary faces where a weight vanishes the structure of the heat kernel is radically different, and these arguments do not apply.

## Sources

- C. L. Epstein and R. Mazzeo, *Harnack inequalities and heat-kernel estimates for degenerate diffusion operators arising in population biology*, *Applied Mathematics Research eXpress* 2016(2) (2016), 217–280, <https://doi.org/10.1093/amrx/abw002>; preprint arXiv:1406.1426, <https://doi.org/10.48550/arXiv.1406.1426>.
