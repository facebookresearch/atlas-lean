# Keyfitz's life-table entropy and proportional changes in mortality

Let $\mu \ge 0$ be a locally integrable force of mortality on $[0, \infty)$, $l(x) = \exp(-\int_0^x \mu)$ the survivorship, $e_0 = \int_0^\infty l$ the life expectancy at birth, $e^\dagger = -\int_0^\infty l \ln l$ the life disparity and $H = e^\dagger/e_0$ Keyfitz's entropy, as defined in Aburto, Alvarez, Villavicencio and Vaupel (2019, Section 1); assume $e_0 < \infty$ and $e^\dagger < \infty$. Under the proportional change $\mu^* = (1 + \delta)\mu$ the survivorship becomes $l^{1+\delta}$, so $e_0(\delta) = \int_0^\infty l^{1+\delta}$. For $\delta > 0$ the difference quotients $(l^{1+\delta} - l)/\delta$ are dominated by $l\,|\ln l|$, so by dominated convergence

$$\frac{d e_0}{d\delta}\Big|_{\delta = 0^+} = \int_0^\infty l \ln l = -e^\dagger = -H e_0,$$

and $e_0(\delta)/e_0 = 1 - \delta H + o(\delta)$ as $\delta \downarrow 0$: $H$ is the elasticity of life expectancy with respect to a proportional change in mortality (Keyfitz 1977, as stated by Aburto et al.). The two-sided derivative at $0$ holds when in addition $\int_0^\infty l^{1-\varepsilon}|\ln l| < \infty$ for some $\varepsilon > 0$. The same value follows from the formula $\dot e_0 = \int_0^\infty \rho(x) w(x)\, dx$ of Aburto et al. (eq. (4)) with constant rate of mortality improvement $\rho$, since $\int_0^\infty \mu(x) l(x) e(x)\, dx = e^\dagger$.

## Expansion

1. The model: survivorship from a force of mortality, life expectancy, life disparity and the entropy $H$ (with $H \ge 0$ since $l \le 1$).
2. The identity $l^* = l^{1+\delta}$ for proportional hazards.
3. Differentiation under the integral by dominated convergence, with the domination hypothesis for each side of $\delta = 0$.
4. The identity $e^\dagger = \int_0^\infty d(a) e(a)\, da$ with $d = \mu l$ (Goldman and Lord; Vaupel), and the agreement with the time-derivative formula for $e_0$.

## Sources

- J. M. Aburto, J.-A. Alvarez, F. Villavicencio and J. W. Vaupel, The threshold age of the lifetable entropy, Demographic Research 41 (2019), article 4, 83–102, Sections 1 and 2.1, eq. (4). <https://doi.org/10.4054/DemRes.2019.41.4>
- Original result: N. Keyfitz, What difference would it make if cancer were eradicated? An examination of the Taeuber paradox, Demography 14 (1977), 411–418. <https://doi.org/10.2307/2060587> The elasticity interpretation of $H$ follows Aburto et al. (2019).
