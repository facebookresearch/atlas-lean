# Front speed and fluctuations of the boundary-modified contact process at criticality

**Model.** The boundary-modified contact process $\xi_t \subset \mathbb{Z}$ is a one-dimensional epidemic in which infected sites recover at rate $1$ (becoming susceptible again), every infected site infects each nearest neighbor at the interior rate $\lambda_i$, except that the rightmost infected site $\mathcal R(\xi_t)$ infects $\mathcal R(\xi_t) + 1$ and the leftmost $\mathcal L(\xi_t)$ infects $\mathcal L(\xi_t) - 1$ at the edge rate $\lambda_e$. The *right-edge-modified* process $\eta_t$ changes only the rightmost outward rate. Let $\lambda_c$ be the critical rate of the ordinary contact process on $\mathbb{Z}$, and take

$$\lambda_i = \lambda_c, \qquad \lambda_e = \lambda_c + \varepsilon, \quad \varepsilon > 0,$$

so the bulk is exactly critical and only the invasion front is boosted. Let $\Sigma^\ominus$ be the configurations with infinitely many infected sites to the left of the origin and finitely many to the right, and $\tilde\mu$ the invariant law of $\eta$ seen from its right edge (supported on $\Sigma^\ominus$).

**Theorem.** With these rates:
1. *(Law of large numbers.)* If $\eta_0 \in \Sigma^\ominus$, then almost surely $\mathcal R(\eta_t)/t \to \alpha$, where $\alpha = \mathbb{E}[\mathcal R(\tilde\eta_1)]$ for $\tilde\eta_0 \sim \tilde\mu$, and $\alpha \ge \varepsilon$.
2. *(Functional CLT.)* If $\eta_0 \in \Sigma^\ominus$, then $\big(n^{-1/2}(\mathcal R(\eta_{nt}) - \alpha n t)\big)_{t \ge 0} \Rightarrow (W_t)_{t\ge0}$, a Brownian motion with variance parameter $\sigma^2 > 0$ not depending on $\eta_0$.
3. *(Front deviations.)* From $\tilde\mu$, for every $\gamma \in [0, \frac13)$ and $b > 0$, $\mathbb{P}\big(|\mathcal R(\tilde\eta_t) - \alpha t| > b\, t^{1-\gamma}\big) \le c\, e^{-c' t^{a}}$ with $a = a(\gamma) > 0$ independent of $\varepsilon$.
4. *(Stretched-exponential extinction bounds.)* For either process started from $n < \infty$ infected sites, with $\tau^\emptyset$ the extinction time, $\mathbb{P}(t < \tau^\emptyset < \infty) \le c\,e^{-c' t^a}$ and $\mathbb{P}(\tau^\emptyset < \infty) \le c\, e^{-c' n^a}$, with $a > 0$ independent of $\varepsilon$ and $n$.

So boosting only the frontier transmission rate by any $\varepsilon > 0$ makes a critical epidemic invade at positive linear speed, with diffusive Gaussian front fluctuations.

## Expansion

The modified process is neither attractive nor sub-additive, so the classical proofs for the supercritical contact process do not apply. Positive speed at criticality uses the half-line survival result of Andjel and Rolla, and the stretched-exponential bounds use box-crossing estimates for critical oriented percolation (Duminil-Copin–Tassion–Teixeira): a critical cluster crosses a $w(n) \times n$ box with $w(n) \le c n^{1-\delta}$ with probability bounded below, which gives the exponent $a$. Seen from its right edge the process is stationary under $\tilde\mu$ and its increments are $\alpha$-mixing with stretched-exponential mixing rate, so the Ibragimov–Davydov functional CLT for mixing sequences yields Brownian fluctuations.

## Sources

- Andrew Heeszel, "Limiting Speed and Fluctuations for the Boundary Modified Contact Process", arXiv:2512.04431 (2025), Section 1 (model, $\Sigma^\ominus$, $\tilde\mu$) and Theorems 1–5, <https://doi.org/10.48550/arXiv.2512.04431>.
