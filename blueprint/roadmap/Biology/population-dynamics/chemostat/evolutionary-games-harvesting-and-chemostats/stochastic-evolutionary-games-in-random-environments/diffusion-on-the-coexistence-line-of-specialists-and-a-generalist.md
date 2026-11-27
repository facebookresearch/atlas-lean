# Diffusion on the coexistence line of specialists and a generalist in a random environment

**Model.** A Moran-type population of constant size $N$ contains two specialists $C$ and $H$ and a generalist $M$. The environment is in state **c** with probability $q$ and in state **h** with probability $1-q$. Fitness is $1$ for a specialist in its own environment and $0$ otherwise, and $1/2$ for $M$ in either environment. Each individual dies at rate $1$ and is replaced by an offspring chosen with probability proportional to fitness, averaged over the environment, so the birth weights are $\lambda_C = q\frac{2C}{2C + M}$, $\lambda_H = (1-q)\frac{2H}{2H+M}$, and $\lambda_M = q\frac{M}{2C+M} + (1-q)\frac{M}{2H+M}$. In the coordinates $d = (C - H)/N$, $m = M/N$, on the triangle $S = \{|d| + m \le 1,\ m \ge 0\}$, the mean drift is

$$
b_d = -\frac{(1 - m - d^2)(1 + d - 2q)}{(1+d)(1-d)}, \qquad b_m = \frac{d\, m\, (1 + d - 2q)}{(1+d)(1-d)}.
$$

**Proposition (deterministic phase).** If $y^N_t = Y_{Nt}/N$ starts near $\bar y_0 = (d_0, m_0)$ with $1 - d_0^2 > \varepsilon$ and $0 < m_0 < 1$, then until $1 - (d_t^N)^2 \le \varepsilon$,

$$
\mathbb{E}\Big(\sup_{t \le T \wedge \tau_\varepsilon^N}\|y^N_t - \bar y_t\|^2\Big) \le \frac{L(N,T)^2}{N}, \qquad \sup_N L(N,T) < \infty,
$$

where $\bar y$ solves $\dot{\bar y} = b(\bar y)$. The line $\Gamma = \{d = 2q - 1\}$ consists of fixed points, is stable, and attracts all of $S$ except the three corners: $\varphi = (d - 2q + 1)^2$ is a Lyapunov function, with $\nabla\varphi \cdot b = -2(1 - m - d^2)(1 + d - 2q)^2/((1-d)(1+d)) \le 0$. Along trajectories $m$ moves with the sign of $d(1 + d - 2q)$: it increases where $d$ and $d - (2q-1)$ have the same sign and decreases where $d$ lies strictly between $0$ and $2q - 1$ (e.g. $q = 0.75$, $(d,m) = (0.25,0.5)$ gives $b_m = -0.033$), so it is monotone non-decreasing for every start only when $q = 1/2$. (The source states that $m$ never decreases.)

**Proposition (diffusive phase).** On the slower time scale, $y^{N^2}_t = Y_{N^2 t}/N$ started within $N^{-\delta}$ of $\Gamma$ ($\delta \in (0, 1/2)$) stays within $N^{-\delta}$ of $\Gamma$ with probability tending to $1$ until the first species goes extinct. The stopped process converges weakly to a one-dimensional diffusion $\boldsymbol m^*_t$ on $\Gamma$, whose drift and diffusion coefficients come from projecting the two-dimensional noise along the deterministic flow onto $\Gamma$, stopped at the boundary of $\Gamma$.

## Depends on

- [Moran model fixation probability](../../../../population-genetics/moran-model/moran-fixation.md)

## Expansion

This is a separation of time scales. On time scale $N$ the law of large numbers for density-dependent jump processes makes selection dominate: the specialists' difference $d$ quickly relaxes to $2q - 1$, while the generalist share $m$ drifts with the sign of $b_m$. Coexistence of the two specialists in proportions fixed by $q$ is thus deterministically stable, but on $\Gamma$ the mean drift vanishes. On time scale $N^2$, demographic noise moves the state along $\Gamma$. The projection map $\Phi$, which sends a point to its limit on $\Gamma$ under the flow, kills the large normal component of the drift ($\nabla\Phi \cdot b = 0$), leaving an Itô correction and a noise term. The result is a regular diffusion for the position on the coexistence line, whose exit gives the first extinction.

## Sources

- Lea Popovic, Liam Peuckert, "Diffusion dynamics on the coexistence subspace in a stochastic evolutionary game", Journal of Mathematical Biology 80 (2020), 1655–1682, <https://doi.org/10.1007/s00285-020-01476-z>. Published version of arXiv:1802.03623, cited next; locators there refer to the arXiv version.
- Lea Popovic, Liam Peuckert, "Difffusion Dynamics on the Coexistence Subspace in a Stochastic Evolutionary Game", arXiv (2018). Section 2, Proposition 1, Proposition 2, Eqs. for the drift and the diffusion on $\Gamma$. <https://doi.org/10.48550/arXiv.1802.03623>
