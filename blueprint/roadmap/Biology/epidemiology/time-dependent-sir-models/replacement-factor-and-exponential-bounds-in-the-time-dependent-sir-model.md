# Replacement factor and exponential bounds in the time-dependent SIR model

**Model.** In a closed population, let $s,i,r$ be the susceptible, infected and removed fractions. The transmission rate $\beta(t)$, death rate $\mu(t)$ and recovery rate $\gamma(t)$ are continuous and positive, and the total removal rate is $\rho(t)=\mu(t)+\gamma(t)$:
$$s'=-\beta(t)si,\qquad i'=\beta(t)si-\rho(t)i,\qquad r'=\rho(t)i .$$
Define the *reproduction factor* $\sigma(t)=\beta(t)/\rho(t)$ and the *replacement factor* $\sigma_s(t)=\beta(t)s(t)/\rho(t)$, a time-dependent effective reproduction number.

**Theorem.**

1. If $i(t)>0$ then $s$ is strictly decreasing and $r$ strictly increasing; both are constant where $i=0$.
2. $i'(t)$ has the sign of $\sigma_s(t)-1$. The epidemic grows when $\sigma_s>1$, declines when $\sigma_s<1$, and stagnates when $\sigma_s=1$. Since $s\le1$, $\sigma(t)<1$ implies decline. If $\sigma(t)>1$, the epidemic grows exactly while $s(t)>1/\sigma(t)$.
3. *(Exponential decay.)* If $\sigma_s(t)\le\sigma_{\max}<1$ on $[t_0,t_1]$ and $\rho_{\min}=\min_{[t_0,t_1]}\rho$, then
$$i(t)\le i(t_0)\,e^{-\rho_{\min}(1-\sigma_{\max})(t-t_0)},\qquad t\in[t_0,t_1].$$
4. *(Exponential growth.)* If $\sigma_s(t)\ge\sigma_0>1$ on $[t_0,t_1]$, then
$$i(t)\ge i(t_0)\,e^{\rho_{\min}(\sigma_0-1)(t-t_0)},\qquad t\in[t_0,t_1].$$

## Expansion

Write $i'/i=\rho(t)(\sigma_s(t)-1)$ and integrate: $i(t)=i(t_0)\exp\int_{t_0}^t\rho(u)(\sigma_s(u)-1)\,du$. Bounding $\sigma_s-1$ by $\sigma_{\max}-1<0$ or $\sigma_0-1>0$, and $\rho$ from below by $\rho_{\min}$, gives the two estimates. With time-varying rates the herd-immunity threshold $s=1/\sigma(t)$ moves, so an epidemic can switch between growth and decay several times as interventions or variants change $\beta(t)$. This cannot happen in the constant-coefficient SIR model, where $i$ has a single peak. Fitting $\beta(t)$ and $\rho(t)$ to case and removal data and tracking $\sigma_s(t)$ therefore classifies each period of an epidemic as growing or declining, with explicit exponential rates.

## Sources

- R. H. Madi, S. M. Moufawad, N. R. Nassif, "Data-Driven Models for studying the Dynamics of the COVID-19 Pandemics", arXiv:2311.14682 (2023): Section 2 (time-dependent IR and SIR models), Theorem 1 (monotonicity of $s$ and $r$), Theorem 2 and Corollaries 1–2 (threshold behaviour), Theorems 3–4 (exponential decay and growth bounds). <https://doi.org/10.48550/arXiv.2311.14682>
