# Global stability of the parasite-free state in an age-structured SIRS–SI malaria model

**Model.** Susceptible, infectious and recovered humans of age $a \ge 0$ at time $t$, $s_h, i_h, r_h$, and susceptible and infectious mosquitoes $S_v, I_v$ satisfy

$$ \begin{aligned} (\partial_t + \partial_a)s_h &= -\beta_v(a)I_v(t)\,s_h - \mu_h(a)s_h + r_2(a)r_h, \qquad (\partial_t + \partial_a)r_h = r_1(a)i_h - (r_2(a) + \mu_h(a))r_h,\\ (\partial_t + \partial_a)i_h &= \beta_v(a)I_v(t)\,s_h - (\mu_h(a) + \delta(a) + r_1(a))i_h,\\ S_v' &= \Lambda_v - \lambda_v(t)S_v - \mu_v S_v, \qquad I_v' = \lambda_v(t)S_v - \mu_v I_v, \qquad \lambda_v(t) = \int_0^\infty \beta_h(a)i_h(t,a)\,da, \end{aligned} $$

with boundary condition $(s_h, i_h, r_h)(t,0) = (\Lambda_h, 0, 0)$. Assume $\Lambda_h, \Lambda_v, \mu_v > 0$, that $\beta_v, \beta_h, \mu_h, \delta, r_1, r_2$ are nonnegative and essentially bounded, that $\mu_h(a) \ge \mu_0 > 0$ a.e. and $\mu_v \ge \mu_0$, and that $\int_0^\infty\int_0^\infty \beta_h(a+s)\beta_v(a)e^{-\mu_0(a+s)}\,da\,ds > 0$. The parasite-free equilibrium is $E_0 = (s_h^0, 0, 0, S_v^0, 0)$ with $s_h^0(a) = \Lambda_h e^{-\int_0^a \mu_h(u)\,du}$ and $S_v^0 = \Lambda_v/\mu_v$.

**Theorem.**

1. The system generates a unique global strongly continuous semiflow of nonnegative mild solutions, with total human density bounded by that of the disease-free age profile and orbits relatively compact.
2. The basic reproduction number (spectral radius of the next-generation operator) is

$$ \mathcal R_0 = \sqrt{\frac{S_v^0}{\mu_v}\int_0^\infty\!\!\int_0^\infty \beta_h(\xi + s)\,\beta_v(\xi)\,s_h^0(\xi)\,e^{-\int_\xi^{\xi+s}(\mu_h(u) + r_1(u) + \delta(u))\,du}\,d\xi\,ds}. $$

3. If $\mathcal R_0 < 1$, $E_0$ is locally asymptotically stable; if $\mathcal R_0 > 1$, it is unstable.
4. If $\mathcal R_0 \le 1$, $E_0$ is globally asymptotically stable in the nonnegative cone (globally attractive and Lyapunov stable, including at $\mathcal R_0 = 1$). In particular no backward bifurcation occurs.
5. Without loss of immunity ($r_2 \equiv 0$), or with age-independent parameters, there is a unique endemic equilibrium when $\mathcal R_0 > 1$; with both simplifications it is locally asymptotically stable.

## Expansion

The inner integrand follows one infection: a human infected at age $\xi$ (at rate $\beta_v(\xi)$ per mosquito, with $s_h^0(\xi)$ susceptibles available) remains infectious to age $\xi + s$ with the survival factor in the exponent and infects mosquitoes at rate $\beta_h(\xi + s)$, while the factor $S_v^0/\mu_v$ combines the susceptible mosquito pool exposed to that infectiousness with the mean lifetime $1/\mu_v$ of each mosquito it infects; the square root reflects the two-host generation (human to mosquito to human). Well-posedness comes from a Hille–Yosida operator on an extended state space and Lipschitz nonlinearity on bounded sets, local stability from the essential growth bound being below $-\mu_0$ so that only finitely many eigenvalues matter, and global stability from a Lyapunov functional $L_0$ built from the age-weighted infectious class and the infected mosquitoes, applied on compact $\omega$-limit sets together with LaSalle-type invariance.

## Sources

- Seraphin Djaoue, Quentin Richard, Antoine Perasso, Irépran Damakoa, "Global stability in an age-structured SIRS malaria transmission model", arXiv:2603.15201 (2026), Section 2 (system (1), Assumption 1, Propositions 1–3, Theorem 1), Section 3.1 (Equation for $\mathcal R_0$, Assumption 2, Theorem 2), Sections 3.2–3.4 (Lemma 1, Propositions 4–6, Theorems 3–5), Section 3.5 (Theorems 6–8). <https://doi.org/10.48550/arXiv.2603.15201>. Published version: Nonlinear Analysis: Real World Applications 94 (2027), article 104716, <https://doi.org/10.1016/j.nonrwa.2026.104716>; locators above refer to the arXiv version.
