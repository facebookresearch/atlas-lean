# Threshold dynamics of the SIRC model with infection-driven immune escape

**Model.** Population fractions of susceptible $S$, infectious $I$, recovered (fully immune) $R$ and cross-immune $C$ individuals satisfy
$$\begin{aligned}
\dot S &= \mu(1-S) - \beta SI + (1+\varepsilon_2 g(x))\gamma C,\\
\dot I &= \beta SI + \sigma\beta CI - (\mu+\alpha)I,\\
\dot R &= (1-\sigma)\beta CI + \alpha I - \mu R - (1+\varepsilon_1 g(x))\delta R,\\
\dot C &= (1+\varepsilon_1 g(x))\delta R - \beta CI - \mu C - (1+\varepsilon_2 g(x))\gamma C,
\end{aligned}$$
with $\mu,\beta,\alpha,\delta,\gamma>0$, $\sigma\in[0,1]$ and $\varepsilon_1,\varepsilon_2\ge 0$. The smooth function $g\ge 0$ depends only on $(S,I)$, vanishes when $I=0$, and $g=0$ implies $SI=0$; it accelerates waning of immunity ($R\to C\to S$) while infection circulates, modelling infection-driven immune escape. The state space is the simplex $\Omega=\{S,I,R,C\ge0,\ S+I+R+C=1\}$, which is forward invariant. Let $\mathcal{R}_0 = \beta/(\mu+\alpha)$.

**Theorem.**

1. The disease-free equilibrium $(1,0,0,0)$ is the unique equilibrium with $I=0$; it is hyperbolic for $\mathcal{R}_0\ne1$, locally asymptotically stable for $\mathcal{R}_0<1$ and unstable for $\mathcal{R}_0>1$.
2. If $\mathcal{R}_0>1$, then for every $\varepsilon_1,\varepsilon_2\ge0$ there is an endemic equilibrium $x^{*}$ with $S^{*},I^{*},R^{*},C^{*}>0$, and the flow is uniformly persistent in $I$: there is $\eta_0>0$ with $\liminf_{t\to\infty} I(t) > \eta_0$ whenever $I(0)>0$.

## Expansion

At the disease-free equilibrium the $I$-equation linearises to $\dot I=(\beta-\mu-\alpha)I$, and the immune-escape terms vanish because $g=0$ there, so the eigenvalue $\beta-\mu-\alpha$ decides stability. For persistence, the boundary $\{I=0\}$ is invariant and every trajectory in it tends to the disease-free equilibrium, which repels into the interior when $\mathcal{R}_0>1$; acyclicity of the boundary dynamics gives uniform weak and then strong persistence, and a compact attractor in the interior contains an equilibrium.

## Sources

- D. R. Ramírez-Gutiérrez, L. Lóczi, C. Muñoz-Moncayo, D. I. Ketcheson, "Compartmental epidemiological models with infection-driven immune escape", arXiv:2610.01111, Section 2, Proposition 2.4; Section 3, Theorem 3.1, Corollary 3.9 and Proposition 3.13. <https://doi.org/10.48550/arXiv.2610.01111>
