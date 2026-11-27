# Optimal radiotherapy fractionation with dose bounds: minimizing organ-at-risk effect

With the linear-quadratic effects $E_T(N,d) = \alpha_T \sum_i d_i + \beta_T \sum_i d_i^2$ on the tumor and $E_{OAR}(N,d) = \alpha_0\delta \sum_i d_i + \beta_0\delta^2 \sum_i d_i^2$ on the organ at risk (OAR), as in [the tumor-maximizing problem](optimal-fractionation-maximizing-tumor-effect-under-dose-bounds.md), the palliative problem $(P_2)$ is to minimize $E_{OAR}(N,d)$ over $N \in \mathbb N$ and $d \in \mathbb R^N$ subject to a required tumor effect $E_T(N,d) \ge \gamma_T$ and dose bounds $0 < d_{\min} \le d_i \le d_{\max}$. Write $\varphi_T(r) = \alpha_T r + \beta_T r^2$,

$$ \lambda_T = \max\left\{1, \frac{\gamma_T}{\varphi_T(d_{\max})}\right\}, \qquad \rho_T = \max\left\{1, \frac{\gamma_T}{\varphi_T(d_{\min})}\right\}, \qquad \omega_\delta = \frac{\alpha_T}{\beta_T} - \frac{\alpha_0}{\beta_0\delta}, $$

and $\bar d_1(N)$ for the equal dose meeting the tumor target exactly, $N\varphi_T(\bar d_1) = \gamma_T$:

$$ \bar d_1(N) = \frac{-\alpha_T N + \sqrt{(\alpha_T N)^2 + 4\beta_T N \gamma_T}}{2\beta_T N}. $$

$(P_2)$ always has a solution when $d_{\min} > 0$. Assume $\lceil\lambda_T\rceil < \lfloor\rho_T\rfloor$.

- If $\omega_\delta > 0$ (**hyperfractionation**): when $\rho_T \in \mathbb N$, $\rho_T \ge 2$, the unique solution is $N = \rho_T$ fractions at $d_{\min}$; when $\rho_T \notin \mathbb N$, the unique solution is either $N = \lceil\rho_T\rceil$ fractions at $d_{\min}$ or $N = \lfloor\rho_T\rfloor$ equal fractions of dose $\bar d_1(\lfloor\rho_T\rfloor)$, whichever gives the smaller OAR effect.
- If $\omega_\delta < 0$ and $\rho_T > 1$ (**hypofractionation**): a solution has $N = \lceil\lambda_T\rceil$ fractions, $K$ of them at $d_{\min}$, at most one at an intermediate dose $d^*$ and the rest at $d_{\max}$, where $K = \lfloor (N\varphi_T(d_{\max}) - \gamma_T)/(\varphi_T(d_{\max}) - \varphi_T(d_{\min})) \rfloor$ and $\varphi_T(d^*) = \gamma_T - K\varphi_T(d_{\min}) - (N-K-1)\varphi_T(d_{\max})$ (no intermediate dose when that ratio is an integer).
- If $\omega_\delta = 0$ and $\rho_T > 1$, every feasible pair with $E_T = \gamma_T$ is optimal.

The optimal number of fractions increases with $\gamma_T$, decreases with $\alpha_T$ and $\beta_T$, and does not depend on $\alpha_0$, $\beta_0$ or $\delta$. The choice between hyper- and hypofractionation is decided by the sign of $\omega_\delta$ alone, exactly as in the tumor-maximizing problem.

## Depends on

- [Optimal radiotherapy fractionation with dose bounds: maximizing tumor effect](optimal-fractionation-maximizing-tumor-effect-under-dose-bounds.md)

## Expansion

For fixed $N \in [\lambda_T, \rho_T)$ the tumor constraint is active at any optimum. On the sphere $E_T = \gamma_T$, $\sum d_i^2 = (\gamma_T - \alpha_T \sum d_i)/\beta_T$, so $E_{OAR} = \beta_0\delta^2\gamma_T/\beta_T - \beta_0\delta^2\, \omega_\delta \sum d_i$: minimizing the OAR effect means maximizing the total dose when $\omega_\delta > 0$ (equal doses) and minimizing it when $\omega_\delta < 0$ (doses at the box corners plus one remainder). Stepping across the finitely many feasible $N$ then selects the extreme admissible number of fractions; for $\omega_\delta > 0$ the candidates are the two integers around $\rho_T$, because at $N \ge \rho_T$ fractions at $d_{\min}$ already meet the target. When $\omega_\delta > 0$, the bound $d_{\min} > 0$ is necessary: with $d_{\min} = 0$ an explicit example has its infimum approached only by ever more, ever smaller fractions, and not attained. These are Theorems 9–13, Proposition 5 and Corollary 2 of the source.

## Sources

- L. A. Fernández and L. Fernández, *Analytical solution to the radiotherapy fractionation problem including dose bound constraints*, arXiv:2102.08237 (2021), Section "Minimizing the effect of radiation on the organs at risk", Theorems 9–13, Proposition 5, Corollary 2. <https://doi.org/10.48550/arXiv.2102.08237> Published version: Operations Research Forum 3 (2022) 40, <https://doi.org/10.1007/s43069-022-00146-8>.
