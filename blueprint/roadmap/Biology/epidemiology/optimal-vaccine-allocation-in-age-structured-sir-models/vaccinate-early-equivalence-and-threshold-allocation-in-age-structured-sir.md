# Early vaccination and threshold allocation in the age-structured SIR model

**Model.** Let $\mathcal{X} = [0,A]$ be the age interval. Susceptible and infectious densities $S(t,x)$, $I(t,x)$ evolve by

$$\partial_t S = -S\int_{\mathcal{X}}\beta(x,y)\,I(t,y)\,dy - \nu(t,x), \qquad \partial_t I = S\int_{\mathcal{X}}\beta(x,y)\,I(t,y)\,dy - \mu(x)\,I,$$

with continuous positive transmission kernel $\beta$, infection-death rate $\mu$, initial data $(S_0, I_0)$, and vaccination rate $\nu \ge 0$ in the admissible set $\mathcal{V}$ (controls keeping $S \ge 0$). Every infected individual eventually dies, so the number of survivors is

$$\mathcal{N}(\nu) = \int_{\mathcal{X}} S_\infty(x)\,dx + \int_{\mathcal{X}}\int_0^\infty \nu(t,x)\,dt\,dx, \qquad S_\infty = \lim_{t\to\infty} S(t,\cdot).$$

The **optimal vaccination problem** maximizes $\mathcal{N}(\nu)$ over $\nu \in \mathcal{V}$ with total dose $\iint \nu \le K$. The **initial vaccination problem** instead removes $v(x) \in [0, S_0(x)]$ susceptibles before the outbreak and maximizes $\mathcal{N}^\star(v) = \int S^\star_\infty + \int v$ subject to $\int v \le K$, where $S^\star$ solves the system with $\nu \equiv 0$ and $S^\star(0) = S_0 - v$.

**Threshold.** With $\lambda_1$ the principal eigenvalue of $\phi \mapsto \phi - \int \beta(\cdot,y)S_0(y)\mu(y)^{-1}\phi(y)\,dy$, the epidemic does not spread if $\lambda_1 \ge 0$ and spreads if $\lambda_1 < 0$.

**Final-size relation.** For $\nu \in \mathcal{V}$ the solution exists, is unique and nonnegative, $I(t,x) \to 0$, $S(t,x) \to S_\infty(x)$ pointwise, and wherever $S_\infty(x) > 0$, with $\nu_\infty(x) = \int_0^\infty \nu(t,x)\,dt$,

$$S_\infty(x) = S_0(x)\exp\!\Big(\int\frac{\beta(x,y)}{\mu(y)}\big(S_\infty + \nu_\infty - I_0 - S_0\big)(y)\,dy - \int_0^\infty\frac{\nu(t,x)}{S(t,x)}\,dt\Big).$$

**Theorem (vaccinate as early as possible).**

$$\sup_{\nu\in\mathcal{V},\ \iint\nu\le K}\mathcal{N}(\nu) = \sup_{v\in\mathcal{V}^\star,\ \int v\le K}\mathcal{N}^\star(v).$$

Indeed, for any $\nu$, the survivors are at most those obtained by giving the same doses $\nu_\infty$ at time $0$ ($S_\infty \le S^\star_\infty$), and every initial allocation is approximated by admissible time-dependent controls.

**Theorem (optimal allocation for susceptibility-only kernels).** Suppose $\beta(x,y) = \beta(y)$ depends only on the infector's age, the level sets $\{\beta/\mu = s\}$ have measure zero, and

$$K < \min_{\mathcal{X}}\Big(\frac{\mu}{\beta}\Big)\int_{\mathcal{X}}\frac{\beta}{\mu}S_0.$$

Then the threshold strategy $v_K = S_0\,\mathbf{1}_{\{\beta/\mu > s_K\}}$, with $s_K$ chosen so that $\int_{\{\beta/\mu > s_K\}} S_0 = K$, maximizes the number of survivors: vaccinate completely the age groups with the largest ratio of infectiousness to infection-death rate.

## Expansion

Writing $S$ in Duhamel form turns the SIR system into a nonlinear integral equation for $S$ alone. Vaccinating later lets the vaccinated individuals take part in transmission for longer and costs the factor $\exp(-\int \nu/S)$, so a comparison principle for the integral operator $U \mapsto U - \int k(\cdot,y)g(U(y))\,dy$ (with $g$ concave and a positive principal eigenvalue guaranteeing stability) gives $S_\infty \le S^\star_\infty$. For a kernel depending only on $y$, the final state depends on $v$ only through the scalar $\sigma_0(v) = \int (\beta/\mu)v$, and a larger $\sigma_0$ yields a larger final susceptible pool; a bathtub (rearrangement) argument then shows that $\sigma_0$ is maximized at fixed dose $m$ by filling the ages with largest $\beta/\mu$ first.

## Sources

- Luis Almeida, Romain Ducasse and Elisa Paparelli, "Optimizing vaccine allocation in an age-structured SIR model", arXiv:2605.18256 (2026), Section 1 (Theorems 1–4) and Section 2 (Propositions 1–6, Lemmas 2–8), <https://doi.org/10.48550/arXiv.2605.18256>.
