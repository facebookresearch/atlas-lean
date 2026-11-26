# Bet-hedging threshold for competing phenotype-structured populations

**Model.** Populations $i \in \{H, L\}$ with densities $n_i(x, t)$ over a phenotype $x \in \mathbb{R}$ compete through total size $\rho = \rho_H + \rho_L$, $\rho_i = \int n_i\,dx$:

$$\partial_t n_i = \beta_i\, \partial_{xx} n_i + \big(p(x, S(t)) - d\rho(t)\big) n_i, \qquad \beta_H > \beta_L > 0,$$

where $\beta_i$ is the rate of spontaneous phenotypic variation, $d > 0$ the competition rate and $S(t) \ge 0$ a given nutrient level. With maximal proliferation rate $\gamma$ in both extreme environments, the net proliferation rate is the quadratic fitness landscape

$$p(x, S) = \gamma\big(g(S) - (x - \varphi(S))^2\big), \qquad \varphi(S) = \frac{1}{1+S}, \quad g(S) = \frac{S}{1+S} + \frac{1}{(1+S)^2},$$

so $\varphi(S) \in (0, 1]$ is the fittest phenotype (low $S$ favours $x \to 1$) and $\gamma g(S)$ the maximal fitness.

**Gaussian reduction.** For Gaussian initial data, $n_i(\cdot, t)$ stays Gaussian with mass $\rho_i$, mean $\mu_i$ and inverse variance $v_i = 1/\sigma_i^2$ solving

$$\dot v_i = 2(\gamma - \beta_i v_i^2), \qquad \dot\mu_i = \frac{2\gamma}{v_i}(\varphi(t) - \mu_i), \qquad \dot\rho_i = \Big(\gamma g(t) - \beta_i v_i - \gamma(\mu_i - \varphi(t))^2 - d\rho\Big)\rho_i .$$

Thus $\sigma_i^2(t) \to \sqrt{\beta_i/\gamma}$ exponentially fast.

**Constant environment** ($S \equiv \bar S$, $\bar g = g(\bar S)$, $\bar\varphi = \varphi(\bar S)$). Always $\rho_H \to 0$. If $\sqrt{\gamma\beta_L} \ge \gamma\bar g$ both populations go extinct; otherwise

$$\rho_L \to \frac{\gamma\bar g - \sqrt{\gamma\beta_L}}{d}, \qquad \mu_L \to \bar\varphi, \qquad \sigma_L^2 \to \sqrt{\beta_L/\gamma}.$$

**Periodic environment** ($S$ continuous and $T$-periodic). The mean of population $i$ converges to the unique $T$-periodic solution $u_i$ of $\dot u_i = 2\sqrt{\gamma\beta_i}\,(\varphi(t) - u_i)$, whose average equals that of $\varphi$. Define

$$\Lambda_i = \sqrt{\gamma\beta_i} + \frac{\gamma}{T}\int_0^T \big(u_i(s) - \varphi(s)\big)^2 ds .$$

If $\min\{\Lambda_H, \Lambda_L\} \ge \frac{\gamma}{T}\int_0^T g$, both populations go extinct. Otherwise the population $i$ with the smaller $\Lambda_i$ survives, converging to a $T$-periodic size $w_i(t)$ with time average $\frac{1}{d}\big(\frac{\gamma}{T}\int_0^T g - \Lambda_i\big)$, mean $u_i(t)$ and variance $\sqrt{\beta_i/\gamma}$, while the other goes extinct.

## Expansion

Substituting $n_i \propto \exp(-v_i(x-\mu_i)^2/2)$ into the PDE and matching powers of $x - \mu_i$ gives the ODEs: diffusion contributes $\beta_i(v_i^2(x-\mu_i)^2 - v_i)$ and the quadratic landscape contributes $-\gamma(x - \varphi)^2$. $\Lambda_i$ is the long-run fitness cost of population $i$: $\sqrt{\gamma\beta_i}$ is the variance load of maintaining phenotypic spread, and the integral is the lag load from tracking the oscillating optimum with response rate $2\sqrt{\gamma\beta_i}$. In a constant environment the lag load vanishes and lower variability always wins; under fast or large fluctuations, the more variable population lags less and can win, a form of bet-hedging. The competitive exclusion follows from comparing $\frac{d}{dt}\ln\rho_i$ for the two populations, which differ only by $\Lambda_i$ in time average.

## Sources

- A. Ardaševa, R. A. Gatenby, A. R. A. Anderson, H. M. Byrne, P. K. Maini, T. Lorenzi, "Evolutionary dynamics of competing phenotype-structured populations in periodically fluctuating environments", Journal of Mathematical Biology 80 (2020) 775–807, Section 2 (model (3)–(11)) and Section 3 (Proposition 1, Theorem 3 with equations (24)–(34), Lemmas 1–2 and Theorem 4 with equations (49)–(61)), <https://doi.org/10.1007/s00285-019-01441-5>.
