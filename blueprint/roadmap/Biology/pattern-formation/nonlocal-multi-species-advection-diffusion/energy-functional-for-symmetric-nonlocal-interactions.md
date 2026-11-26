# Energy functional for symmetric nonlocal multi-species interactions

On the flat torus $\mathbb T = \prod_{h=1}^n [0, L_h]$ (periodic boundary conditions) consider $N$ species with densities
$u_i(x,t) > 0$ moving by diffusion and nonlocal advection:

$$\frac{\partial u_i}{\partial t} = D_i \Delta u_i + \nabla \cdot \Bigl( u_i \sum_{j=1}^N \gamma_{ij} \nabla (K * u_j) \Bigr), \qquad i = 1, \dots, N,$$

where $D_i > 0$, $\gamma_{ij} \in \mathbb{R}$ ($\gamma_{ij} > 0$: species $i$ moves away from $j$; $\gamma_{ij} < 0$: towards $j$), and the
detection kernel $K$ is symmetric ($K(x) = K(-x)$), non-negative, with $\|K\|_{L^1} = 1$. The masses $p_i = \int_{\mathbb T} u_i\,dx$ are
conserved, so $\bar u = (\bar u_1, \dots, \bar u_N)$, $\bar u_i = p_i/|\mathbb T|$, is a homogeneous steady state.
Write the system in gradient-flow form $\partial_t u_i = \nabla\cdot\bigl[u_i \nabla\bigl(D_i \ln u_i + \sum_j \gamma_{ij} K * u_j\bigr)\bigr]$ and define

$$E[u_1, \dots, u_N] = \int_{\mathbb T} \sum_{i=1}^N u_i \Bigl( D_i \ln u_i + \frac12 \sum_{j=1}^N \gamma_{ij}\, K * u_j \Bigr) dx .$$

**Proposition.** Assume $\gamma_{ij} = \gamma_{ji}$ for all $i, j$ and that solutions with positive initial data stay positive.
1. For any symmetric $K \in L^1(\mathbb T)$, $E$ is continuous on the space of $N$-tuples of continuous positive functions on $\mathbb T$ with the uniform norm. (Continuity in the $L^1$ topology fails: with no interaction, $u_n = 1 - 1/n + e^n \mathbf 1_{[0, e^{-n}/n]}$ on the unit torus converges to $1$ in $L^1$, while $\int u_n \ln u_n \to 1 \ne 0$.)
2. Along trajectories,

$$\frac{dE}{dt} = -\int_{\mathbb T} \sum_{i=1}^N u_i \Bigl| \nabla \Bigl( D_i \ln u_i + \sum_{j=1}^N \gamma_{ij} K * u_j \Bigr) \Bigr|^2 dx \le 0,$$

   with equality iff $\nabla(D_i \ln u_i + \sum_j \gamma_{ij} K * u_j) = 0$ for all $i$, i.e. iff $u$ is a steady state.
3. If $\|K\|_{L^\infty} < \infty$ and the initial data are positive and in $L^1(\mathbb T)^N$, then $E$ is bounded below along the trajectory,
   so $E(u(t)) \to l_{u_0}$ as $t \to \infty$ for a constant $l_{u_0}$ depending on the initial data.

Hence $E$ is a Lyapunov functional: there are no non-stationary time-periodic solutions, and local minimizers of $E$ (under the mass
constraints) are candidate stable steady states, inhomogeneous when $\bar u$ is linearly unstable.

## Depends on

- [Linear instability of the homogeneous state of nonlocal multi-species advection–diffusion](linear-instability-of-the-homogeneous-state.md)

## Expansion

Differentiating $E$ and using the symmetry of $K$ to move the convolution, $\int f\,(K*g) = \int (K*f)\, g$, together with
$\gamma_{ij} = \gamma_{ji}$, the two interaction terms combine and $dE/dt = \int \sum_i \partial_t u_i\, f_i$ with
$f_i = D_i\ln u_i + \sum_j \gamma_{ij}K*u_j + D_i$ (the constant $D_i$ integrates to zero by mass conservation). Substituting the gradient-flow
form and integrating by parts on the torus gives the dissipation formula. The lower bound uses
$\int \gamma u_i (K * u_j) \ge -|\gamma|\,\|u_i\|_{L^1}\|K\|_{L^\infty}\|u_j\|_{L^1}$, conservation of mass, and $u\ln u \ge -1/e$. Positivity of
solutions is proved in one spatial dimension; in higher dimensions it is assumed. (Giunta et al. 2022, Equations 15–27 and
Propositions 1–4.)

## Sources

- V. Giunta, T. Hillen, M. A. Lewis, and J. R. Potts, "Detecting minimum energy states and multi-stability in nonlocal advection–diffusion models for interacting species", Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01824-1> (PMC9585017).
