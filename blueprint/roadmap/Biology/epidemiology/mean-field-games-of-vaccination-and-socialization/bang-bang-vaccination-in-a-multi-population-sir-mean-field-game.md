# Bang-bang vaccination in a multi-population SIR mean field game

A population is split into $K$ groups with fractions $m^k$. A representative agent of group $k$ moves on the states $\{S, I, R\}$ as a continuous-time Markov chain: it is infected at rate $\beta^k \alpha^k_t Z^k_t$, vaccinated into $R$ at rate $\kappa^k \nu^k_t$, and recovers at rate $\gamma^k$, where $\alpha^k_t$ is its socialization level, $\nu^k_t \in [0,1]$ its vaccination effort, and

$$
Z^k_t = \sum_{l=1}^K w(k,l)\, \bar\alpha^l_t(I)\, p^l_t(I)\, m^l
$$

is the infectious contact pressure, with network weights $w(k,l) \in [0,1]$, infected fractions $p^l_t(I)$ and mean socialization $\bar\alpha^l_t(I)$ of infected agents. The agent minimizes over $[0,T]$ the expected cost

$$
\mathbb{E}\int_0^T \Big[\big(c^k_\lambda(\lambda^{k,S}_t - \alpha^k_t)^2 + c^k_\nu \nu^k_t\big)\mathbf{1}_S + \big((\lambda^{k,I}_t - \alpha^k_t)^2 + c^k_I\big)\mathbf{1}_I + (\lambda^{k,R}_t - \alpha^k_t)^2 \mathbf{1}_R\Big]\,dt ,
$$

where $\lambda^{k,e}_t \in (0,1]$ are social-distancing guidelines, $c^k_\nu$ the vaccination cost and $c^k_I$ the cost of being infected. Let $u^k_t(e)$ be the value function.

**Theorem.**

1. A control profile is a multi-population mean field Nash equilibrium if and only if it is given by

$$
\hat\alpha^k_t(S) = \lambda^{k,S}_t + \frac{\beta^k Z^k_t\,(u^k_t(S) - u^k_t(I))}{2c^k_\lambda}, \quad \hat\alpha^k_t(I) = \lambda^{k,I}_t, \quad \hat\alpha^k_t(R) = \lambda^{k,R}_t, \quad \hat\nu^k_t = \mathbf{1}\{\kappa^k u^k_t(S) > c^k_\nu\},
$$

with $(u, p)$ solving the coupled forward–backward ODE system of Kolmogorov and Hamilton–Jacobi equations.
2. Under the paper's regularity assumption, equilibrium vaccination is bang-bang with at most one jump: $\hat\nu^k_t = 1$ for $t < t^k_1$ and $0$ afterwards, where $u^k_{t^k_1}(S) = c^k_\nu/\kappa^k$; if $u^k_0(S) < c^k_\nu/\kappa^k$, no one in group $k$ vaccinates.
3. For a sufficiently short horizon $T$ and $c^k_\nu < c^k_I$ for all $k$, the forward–backward system has at least one Carathéodory solution, hence an equilibrium exists.

## Expansion

Vaccination enters the Hamiltonian linearly, so the optimal effort is the indicator in item 1; the one-jump structure follows by showing that the susceptible value $u^k_t(S)$ crosses the level $c^k_\nu/\kappa^k$ at most once, from above, before the horizon. Socialization is quadratic, so its optimizer is the guideline corrected by the marginal infection risk $u(S) - u(I)$ times the contact pressure. In a population-aware extension, the same one-jump structure holds when $c^k_I$ exceeds the awareness cost, and for fixed contact pressure the vaccination stops no earlier than in the baseline model.

## Sources

- Huaning Liu and Gokce Dayanikli, *Modeling Epidemic Spread with Strategic Vaccination and Socialization: a Mean Field Game Analysis*, arXiv:2604.22946, Theorems 2.2, 2.5 and 2.10 (Section 2) and Theorems 3.1 and 3.2 (Section 3). <https://doi.org/10.48550/arXiv.2604.22946>
