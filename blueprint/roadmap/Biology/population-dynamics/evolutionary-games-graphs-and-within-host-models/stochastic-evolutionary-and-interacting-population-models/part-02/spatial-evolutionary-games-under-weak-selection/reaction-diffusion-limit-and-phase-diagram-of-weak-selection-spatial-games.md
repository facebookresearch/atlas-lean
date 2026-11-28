# Reaction–diffusion limit and phase diagram of weak-selection spatial games

**Voter model perturbations.** On $\mathbb Z^d$ each site holds a strategy in a finite set $S$; with an irreducible finite-range symmetric probability kernel $p$ ($p(0)=0$) whose covariance matrix is $\sigma^2I$, let $f_i(x,\xi) = \sum_y p(y-x)\mathbf 1(\xi(y) = i)$. The voter model flips $x$ from $i$ to $j$ at rate $\mathbf 1(\xi(x) = i) f_j(x,\xi)$. A spatial evolutionary game with payoff matrix $\mathbf 1 + \varepsilon^2 G$ under Birth–Death or Death–Birth updating has flip rates $c^v_{i,j} + \varepsilon^2 h^\varepsilon_{i,j}$ for explicit perturbations $h$.

**Theorem (PDE limit).** Let $d \ge 3$. Rescale space by $\varepsilon$ and time by $\varepsilon^{-2}$, and start from configurations with continuous local densities $v_i$ ($\sum_i v_i = 1$). Then $u^\varepsilon_i(t,x) = \mathbb P\big(\xi^\varepsilon_{t\varepsilon^{-2}}(x) = i\big)$ converges to the solution of

$$\partial_t u_i = \frac{\sigma^2}{2}\Delta u_i + \phi_i(u), \qquad u_i(0,\cdot) = v_i,$$

where $\phi_i(u) = \sum_{j\ne i}\big\langle \mathbf 1(\xi(0) = j)h_{j,i}(0,\xi) - \mathbf 1(\xi(0) = i)h_{i,j}(0,\xi)\big\rangle_u$ is an expectation under the voter-model stationary law with densities $u$.

The reaction term is itself a replicator vector field for a **modified game**. For the $2\times2$ game $\begin{pmatrix}\alpha & \beta\\ \gamma & \delta\end{pmatrix}$, with $u$ the frequency of strategy $1$, the replicator equation is $\dot u = u(1-u)(\beta - \delta + \Gamma u)$ with $\Gamma = \alpha - \beta - \gamma + \delta$, and the limit reaction term is the replicator field of

$$\begin{pmatrix}\alpha & \beta + \theta\\ \gamma - \theta & \delta\end{pmatrix}, \qquad \theta_{BD} = \frac{p_2}{p_1}(\alpha+\beta-\gamma-\delta), \qquad \theta_{DB} = \frac{\bar p_2}{\bar p_1}(\alpha+\beta-\gamma-\delta) - \frac{p(v_1|v_2)}{\kappa\,\bar p_1}(\beta-\gamma),$$

where $p_1,p_2,\bar p_1,\bar p_2, p(v_1|v_2)$ are non-coalescence probabilities of random walks started from $0$ and from one or two random neighbor steps.

**Theorem (two-strategy phase diagram).** Let $\phi$ be the limiting cubic, with interior root $\bar u$ when it exists, and classify: $S_1$ ($\phi'(0) > 0$, $\phi'(1) > 0$, $\bar u$ attracting), $S_2$ ($\phi'(0) < 0$, $\phi'(1) < 0$, $\bar u$ repelling), $S_3$ ($\phi < 0$ on $(0,1)$), $S_4$ ($\phi > 0$ on $(0,1)$). For $\varepsilon < \varepsilon_0(G)$: in $S_3$ strategy $2$ takes over, in $S_4$ strategy $1$ takes over, in $S_2$ strategy $1$ takes over if $\bar u < 1/2$ and strategy $2$ if $\bar u > 1/2$, and in $S_1$ the strategies coexist; moreover for every $\delta > 0$ and $\varepsilon < \varepsilon_0(G,\delta)$, any stationary law concentrated on configurations with infinitely many of each strategy satisfies $\sup_x|\nu(\xi(x) = 1) - \bar u| < \delta$.

## Expansion

Under weak selection, the voter part mixes locally on a fast scale and its stationary laws (in $d \ge 3$) are indexed by densities, while the $\varepsilon^2$ perturbation drives the densities on the slow time scale; the hydrodynamic limit of voter model perturbations gives the reaction–diffusion equation. Duality with coalescing random walks expresses the voter-stationary expectations through the probabilities $p_1, p_2, \dots$, so spatial structure acts only through the shift $\theta$ of the off-diagonal payoffs. For a bistable cubic ($S_2$) the PDE has a traveling front whose speed sign is decided by $\int_0^1\phi$, i.e. by whether $\bar u < 1/2$; comparison with the PDE and block constructions transfer takeover and coexistence to the particle system.

## Depends on

- [Solutions of the replicator equation](../../../../replicator-dynamics/is-solution.md)

## Sources

- Rick Durrett, "Spatial evolutionary games with small selection coefficients", arXiv (2014). Section 3 (voter model perturbations and the PDE limit theorem), Section 6 (two-strategy games, modified game and phase-diagram theorem). <https://doi.org/10.48550/arXiv.1406.5876>. Published version: Electronic Journal of Probability 19 (2014), 1–64, <https://doi.org/10.1214/ejp.v19-3621>; locators above refer to the arXiv version.
