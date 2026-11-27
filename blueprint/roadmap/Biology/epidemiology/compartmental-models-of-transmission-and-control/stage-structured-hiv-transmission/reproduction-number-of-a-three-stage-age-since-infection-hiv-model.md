# Reproduction number of a three-stage age-since-infection HIV model

**Model.** Susceptibles $S(t)$ are recruited at rate $\Lambda$ and die at rate $\mu$. Infected individuals pass through three successive HIV stages, $j=1$ (primary infection), $j=2$ (asymptomatic latency) and $j=3$ (AIDS), with densities $i_j(t,a)$ structured by the time $a$ spent in the current stage:

$$\begin{cases}
\dot S=\Lambda-\mu S-\dfrac SP\displaystyle\int_0^\infty\beta(a)\big(i_1+\varepsilon i_2+\delta i_3\big)(t,a)\,da,\\[4pt]
i_1(t,0)=\dfrac SP\displaystyle\int_0^\infty\beta(a)\big(i_1+\varepsilon i_2+\delta i_3\big)(t,a)\,da,\quad (\partial_t+\partial_a)i_1=-(\gamma_1+d_1)i_1,\\[4pt]
i_2(t,0)=\displaystyle\int_0^\infty\gamma_1i_1\,da,\quad(\partial_t+\partial_a)i_2=-(\gamma_2+d_2)i_2,\\[4pt]
i_3(t,0)=\displaystyle\int_0^\infty\gamma_2i_2\,da,\quad(\partial_t+\partial_a)i_3=-d_3i_3,
\end{cases}$$

with frequency-dependent incidence through $P=S+\int(i_1+i_2+i_3)\,da$. Here $\beta(a)$ is stage-age-dependent infectivity, the factors $\varepsilon,\delta$ scale infectivity in stages 2 and 3, $\gamma_j(a)$ are progression rates, and $d_j\ge\mu$ are death rates; all are bounded, and $\beta,\gamma_j$ are Lipschitz and positive at arbitrarily large ages. Let $D_j(a)=\exp\!\big(-\int_0^a(\gamma_j+d_j)\big)$ for $j=1,2$ and $D_3(a)=\exp\!\big(-\int_0^ad_3\big)$, and set $\Omega_j=\int_0^\infty\beta D_j$ and $\Gamma_j=\int_0^\infty\gamma_jD_j$.

**Theorem.** The model generates a unique strongly continuous, bounded dissipative and asymptotically smooth semiflow with a compact global attractor. With

$$\mathcal R_0=\Omega_1+\varepsilon\,\Omega_2\Gamma_1+\delta\,\Omega_3\Gamma_1\Gamma_2,$$

1. if $\mathcal R_0\le1$ the disease-free equilibrium $E^0=(\Lambda/\mu,0,0,0)$ is the only equilibrium; if $\mathcal R_0>1$ there is also a unique endemic equilibrium $E^*$;
2. $E^0$ is globally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$;
3. if $\mathcal R_0>1$, $E^*$ is locally asymptotically stable, and the semiflow is uniformly persistent for every initial condition with some infected individuals.

With antiretroviral therapy (ART) and a probability of dropping out of treatment, the problem of minimizing AIDS cases plus intervention costs over a horizon $T_f$ has exactly one optimal control when $\frac{T_f}{2}\sum_j1/C_j$ is small, where $C_j$ are the cost weights.

## Expansion

$\Gamma_1$ and $\Gamma_2$ are the probabilities of surviving stage 1 and stage 2 and progressing to the next stage, and $\Omega_j$ is the expected number of infections caused while in stage $j$ by one individual entering it in a fully susceptible population. $\mathcal R_0$ therefore sums the secondary infections produced along the progression path, primary $\to$ latency $\to$ AIDS, weighted by the probability of reaching each stage. Along characteristics the stage densities are explicit, $i_j(t,a)=E_j(t-a)D_j(a)$ for $t\ge a$, so the model reduces to Volterra equations for the boundary fluxes $E_j$. Global stability of $E^0$ follows from a comparison argument on these equations, and persistence from uniform weak persistence combined with the existence of the attractor.

## Sources

- Mboya Ba, Ramsès Djidjou-Demasse, Mountaga Lam, Jean-Jules Tewa, "Optimal intervention strategies of staged progression HIV infections through an age-structured model with probabilities of ART drop out", arXiv:1911.06703 (2019), Section 2 (model, Assumption 1.1, $\mathcal R_0$), Theorem 2.1, Proposition 2.2, Theorem 2.3, Proposition 7.3 and Theorem 8.3, <https://doi.org/10.48550/arXiv.1911.06703>.
