# Number needed to treat from forward sensitivities of a multigroup HIV model

**Setting.** A multigroup HIV transmission model $\dot{\mathbf X} = \mathbf f(\mathbf X,\boldsymbol\theta)$ tracks susceptible and infected numbers $S_j, I_j$ in risk groups $j$ (for example MSM, high- and low-risk heterosexual females, heterosexual males), with natural mortality $\mu$ and fraction $\varepsilon_k$ of susceptibles of group $k$ on PrEP (reducing their force of infection by a factor $1 - \varepsilon_k$ times efficacy). Ignoring disease-induced death, the incidence in group $j$ is $\lambda_j(t) = \dot I_j + \mu I_j$. Define the **forward sensitivities**

$$\sigma^k_j(t) = \frac{\partial S_j}{\partial\varepsilon_k}(t), \qquad \gamma^k_j(t) = \frac{\partial I_j}{\partial\varepsilon_k}(t),$$

so $\gamma^k_k$ is the *direct effect* of PrEP in group $k$ and $\gamma^k_j$, $j\ne k$, its *spillover* on group $j$. With $E_k = \varepsilon_kS_k$ the number of PrEP users, $\partial I_j/\partial E_k = \gamma^k_j/S_k$ and

$$\frac{\partial\lambda_j}{\partial E_k} = \frac{d}{dt}\Big[\frac{\gamma^k_j}{S_k}\Big] + \mu\,\frac{\gamma^k_j}{S_k}.$$

The sensitivities solve the linear variational system $\frac{d}{dt}\big(\partial\mathbf X/\partial\varepsilon_k\big) = D_{\mathbf X}\mathbf f\cdot\partial\mathbf X/\partial\varepsilon_k + \partial\mathbf f/\partial\varepsilon_k$ along the trajectory, with zero initial data.

**Proposition.** The number needed to treat over $[0,T]$, the additional person-years on PrEP in group $k$ per infection prevented in group $j$, satisfies to first order in the PrEP increment

$$\mathrm{NNT}(T) \approx \frac{-T}{\dfrac{\gamma^k_j(T)}{S_k(T)} + \mu\displaystyle\int_0^T\frac{\gamma^k_j(t)}{S_k(t)}\,dt},$$

and, when $\mu T \ll 1$ (here $\mu = 1/50$ per year against a 10-year horizon),

$$\mathrm{NNT}(T) \approx -T\,\frac{S_k(T)}{\gamma^k_j(T)}.$$

For the underlying model, the region of biological states is positively invariant and attracting, and the disease-free equilibrium is locally asymptotically stable if the control reproduction number $\mathbb R_c < 1$ and unstable if $\mathbb R_c > 1$ (globally stable in a special case with no disease-induced death).

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

By definition $\mathrm{NNT} = T\Delta E_k\big/\int_0^T[\lambda_j(t,E_k^0) - \lambda_j(t,E_k^0+\Delta E_k)]\,dt$. Smooth dependence on parameters gives $\lambda_j(t,E_k^0+\Delta E_k) = \lambda_j(t,E_k^0) + \partial_{E_k}\lambda_j\,\Delta E_k + O(\Delta E_k^2)$ uniformly on $[0,T]$, so $\mathrm{NNT}\approx -T/\int_0^T\partial_{E_k}\lambda_j\,dt$. Writing $\partial_{E_k}\lambda_j = e^{-\mu t}\frac{d}{dt}\big[e^{\mu t}\gamma^k_j/S_k\big]$ and integrating by parts, with $\gamma^k_j(0) = 0$, gives the first formula; the integral term is $O(\mu T)$ relative to the boundary term. Linearization at an equilibrium cannot capture spillover, because PrEP in group $k$ acts on group $j$ only through the time-varying prevalence ratios in the forces of infection; the sensitivity system propagates exactly this indirect effect.

## Sources

- Chiara Piazzola, Salman Safdar, Alex Viguerie, Abba B. Gumel, "Analytical and numerical methods for spillover effects in prioritized PrEP for HIV prevention", arXiv (2025). Section 2 (model, Theorems 2.1–2.2, Proposition 2.3, derivation of the spillover equations), Theorem B.1. <https://doi.org/10.48550/arXiv.2508.08035>. Published version: Applied Mathematical Modelling 161 (2027), article 117133, <https://doi.org/10.1016/j.apm.2026.117133>; locators above refer to the arXiv version.
