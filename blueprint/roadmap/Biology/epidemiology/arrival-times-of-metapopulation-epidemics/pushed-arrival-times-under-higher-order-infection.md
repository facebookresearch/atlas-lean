# Pushed arrival times in metapopulation epidemics with higher-order infection

**Model.** Add a group-infection term $\rho s_n j_n^2$ (infection through triads, as in social contagion on simplicial complexes) to the metapopulation SIR model with mobility matrix $\mathrm{P}$ and rate $\gamma$:
$$
\dot s_n = -\alpha s_n j_n - \rho s_n j_n^2 + \gamma\sum_{m\ne n}\mathrm{P}_{nm}(s_m - s_n),\qquad
\dot j_n = \alpha s_n j_n + \rho s_n j_n^2 - \beta j_n + \gamma\sum_{m\ne n}\mathrm{P}_{nm}(j_m - j_n),
$$
with $\alpha>\beta$. Its linearization at the disease-free state coincides with that of the SIR model, so the linear arrival-time estimate is unchanged; yet the nonlinearity now enhances growth, and simulated arrivals are faster than the linear prediction.

**Local dynamics.** For $\rho = 1/\varepsilon\gg 1$ and a city started at $I(0) = \kappa$ with $\kappa<\varepsilon$, geometric singular perturbation (desingularization at the non-normally-hyperbolic slow manifold $\{I=0\}$) gives a slow exponential phase followed by a fast jump to the slow manifold $\{S = 0\}$ at the transition time
$$
\Omega \approx \frac{1}{\alpha-\beta}\log\frac{\varepsilon(\alpha-\beta)}{\kappa},\qquad I(t)\approx\begin{cases}\kappa e^{(\alpha-\beta)t}, & t<\Omega,\\ e^{-\beta(t-\Omega)}, & t\ge\Omega.\end{cases}
$$

**Arrival-time estimate.** With $d_m$ the graph distance from the origin and $\rho_m = \boldsymbol{\delta}_m^{\mathsf T}\mathrm{P}^{d_m}\boldsymbol{\delta}_n$, the cascade argument gives the (formal) arrival time at threshold $\kappa$
$$
t_m \approx \frac{d_m}{\alpha-\beta}\log\!\left(\frac{\kappa\alpha}{\gamma\,\rho_m^{1/d_m}}\right) + d_m\,\Omega .
$$
The leading $\gamma$-dependence is $-\frac{d_m}{\alpha-\beta}\log\gamma$, without the $-\frac{d_m}{\alpha-\beta}\log(-\log\gamma)$ correction of the pulled SIR case, the analogue of a pushed front outrunning the linear spreading speed.

## Expansion

Each city, once its infected fraction reaches the threshold, quickly saturates (fast jump) and then feeds its neighbours with an order-one source $e^{-\beta(t-t_k-\Omega)}$ instead of the small exponentially growing source of the linear model. Solving $\dot j_m \approx (\alpha-\beta)j_m + \gamma\sum_{k:\,d_k = d_m-1}\mathrm{P}_{mk}j_k(t)$ with these sources and using $\rho_m = \sum_{k:\,d_k=d_m-1}\rho_k\mathrm{P}_{mk}$ gives $(\alpha\kappa)^{d_m}/(\gamma^{d_m}\rho_m) = e^{(\alpha-\beta)(t_m - d_m\Omega)}$ by induction on $d_m$.

## Depends on

- [Linearized arrival times bound metapopulation SIR arrival times from below](linearized-arrival-times-bound-metapopulation-sir-arrival-times.md)

## Sources

- A. Armbruster, M. Holzer, N. Roselli, L. Underwood, "Epidemic spreading on complex networks as front propagation into an unstable state", arXiv:2109.11985 (2021), Section 4 (local dynamics, transition-time estimate and arrival-time estimate) and the appendix on the singular perturbation analysis, <https://doi.org/10.48550/arXiv.2109.11985>.
