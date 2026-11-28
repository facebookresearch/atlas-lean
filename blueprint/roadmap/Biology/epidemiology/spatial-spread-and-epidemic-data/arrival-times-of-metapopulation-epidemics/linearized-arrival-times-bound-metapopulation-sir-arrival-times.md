# Linearized arrival times bound metapopulation SIR arrival times from below

**Model.** Consider $N$ cities connected by a row-stochastic mobility matrix $\mathrm{P}$ with mobility rate $\gamma>0$, and SIR dynamics (infection rate $\alpha$, recovery rate $\beta$, $\alpha>\beta$) at each city:

$$
\dot s_n = -\alpha s_n j_n + \gamma \sum_{m\ne n} \mathrm{P}_{nm}(s_m - s_n),\qquad
\dot j_n = \alpha s_n j_n - \beta j_n + \gamma \sum_{m\ne n} \mathrm{P}_{nm}(j_m - j_n),
$$

with $r_n$ recovering from $j_n$ and diffusing in the same way.

**Arrival times.** Seed city $n$ with $s_n(0) = 1-\chi_0$, $j_n(0) = \chi_0\in(0,1)$, all other cities disease free. The nonlinear arrival time $t_{mn}$ at city $m$ is the first time $j_m(t) = \kappa$. Linearizing at the disease-free state, the infected vector decouples and

$$
\mathbf{j}(t) = \chi_0\, e^{(\alpha-\beta-\gamma)t} e^{\gamma \mathrm{P} t}\boldsymbol{\delta}_n ,
$$

and the linear arrival time $\tau_{mn}$ is the smallest positive solution of $\kappa = \chi_0\, \boldsymbol{\delta}_m^{\mathsf T} e^{(\alpha-\beta-\gamma)\tau} e^{\gamma\mathrm{P}\tau}\boldsymbol{\delta}_n$.

**Theorem (linear lower bound).** For all parameters (no smallness of $\gamma$ is needed), $\tau_{mn} < t_{mn}$.

**Small-mobility asymptotics.** Let $d_m$ be the graph distance from $n$ to $m$ and $\rho_m = \boldsymbol{\delta}_m^{\mathsf T}\mathrm{P}^{d_m}\boldsymbol{\delta}_n$ the probability that the random walk with transition matrix $\mathrm{P}$ joins the two cities in exactly $d_m$ steps. Keeping the leading term $k = d_m$ of $e^{\gamma\mathrm{P}\tau} = \sum_k \gamma^k\tau^k\mathrm{P}^k/k!$ gives

$$
\tau_{mn} = \frac{d_m}{\alpha-\beta}\, W\!\left(\frac{1}{\gamma}\,\frac{\alpha-\beta}{d_m}\Big(\frac{d_m!\,\kappa}{\rho_m\chi_0}\Big)^{1/d_m}\right),
$$

with $W$ the Lambert $W$ function, and as $\gamma\to 0$

$$
\tau_{mn} = -\frac{d_m}{\alpha-\beta}\log\gamma - \frac{d_m}{\alpha-\beta}\log(-\log\gamma) - \frac{d_m}{\alpha-\beta}\log\!\left(\frac{d_m}{\alpha-\beta}\Big(\frac{\rho_m\chi_0}{d_m!\,\kappa}\Big)^{1/d_m}\right) + o(1).
$$

So, to leading order, the effective distance is the graph distance and the effective velocity is $(\alpha-\beta)/(-\log\gamma)$; the network enters at order one only through $\rho_m$, and a larger $\rho_m$ gives earlier arrival.

## Proof sketch

The lower bound is a comparison argument: $\bar{\mathbf{s}}\equiv 1$ and $\bar{\mathbf{j}}$ equal to the linear solution form a super-solution, because the SIR nonlinearity only suppresses growth ($s_n\le 1$), so $j_m(t)\le \bar j_m(t)$ and the threshold $\kappa$ is reached no earlier than in the linear system. This mirrors pulled (linearly determinate) fronts for reaction–diffusion equations, whose speed is set by the linearization at the unstable state. The same linear estimate holds for SIS local dynamics, whose linearization at the disease-free state is identical.

## Sources

- Ashley Armbruster, Matt Holzer, Noah Roselli and Lena Underwood, "Epidemic Spreading on Complex Networks as Front Propagation into an Unstable State", *Bulletin of Mathematical Biology* 85 (2023), 4, <https://doi.org/10.1007/s11538-022-01110-7>. Preprint version: arXiv:2109.11985 (2021), Section 2, equations for the linear arrival time and its Lambert-W expansion, and Theorem 2.1, <https://doi.org/10.48550/arXiv.2109.11985>.
