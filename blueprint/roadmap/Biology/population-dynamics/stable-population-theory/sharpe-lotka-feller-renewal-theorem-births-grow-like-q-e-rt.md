# Sharpe–Lotka–Feller renewal theorem for births

In Lotka's renewal model the births $B(t)$ at time $t$ are the births $G(t)$ to women alive at time $0$ plus the births to women born since, $B(t) = G(t) + \int_0^t B(t - a)\, \varphi(a)\, da$, where $\varphi(a) = l(a) m(a)$ is the net maternity function, $l$ the survivorship and $m$ the age-specific fertility (Jones, eqs. (1)–(2)). Let $\varphi \ge 0$ be measurable with $\int_0^\infty \varphi > 0$, let $r$ be the real root of the characteristic equation $\int_0^\infty e^{-ra}\varphi(a)\, da = 1$ (Jones, eq. (4)), and assume $\mu_r = \int_0^\infty a\, e^{-ra}\varphi(a)\, da < \infty$. Let $G \ge 0$ be such that $t \mapsto e^{-rt}G(t)$ is integrable on $[0, \infty)$ and non-increasing, and let $B$ be the solution of the renewal equation that is bounded on compact sets. Then
$$e^{-rt} B(t) \to Q = \frac{1}{\mu_r}\int_0^\infty e^{-rt} G(t)\, dt \qquad (t \to \infty),$$
so births ultimately grow like $Q e^{rt}$. The exponential solutions $c\,e^{rt}$ of the homogeneous renewal equation are characterized by the [renewal equation for exponential growth](../../../Biology/epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff.md); the theorem shows that every solution of the inhomogeneous equation with $G$ as above is asymptotic to the exponential solution with $c = Q$.

The derivation is explicit. Put $B_r(t) = e^{-rt}B(t)$, $G_r(t) = e^{-rt}G(t)$ and $f(a) = e^{-ra}\varphi(a)$. Multiplying the renewal equation by $e^{-rt}$ gives $B_r = G_r + B_r * f$, and $f$ is a probability density with mean $\mu_r$. Hence $B_r(t) = G_r(t) + \int_0^t G_r(t - x)\, u(x)\, dx$ with $u = \sum_{n \ge 1} f^{*n}$ the renewal density of the renewal process with inter-renewal density $f$, and the key renewal theorem for a non-increasing integrable function (as stated in the renewal theory article) gives $\int_0^t G_r(t - x) u(x)\, dx \to \mu_r^{-1}\int_0^\infty G_r$, while $G_r(t) \to 0$ because $G_r$ is non-increasing and integrable.

## Expansion

1. The model: the renewal equation for births with the initial-population term $G$, and existence and uniqueness of its solution bounded on compact sets.
2. The reduction by the factor $e^{-rt}$ to a renewal equation with a probability density $f$, and the representation of its solution through the renewal density $u$.
3. The key renewal theorem in the form used here, and its extension to directly Riemann integrable $G_r$ (the form in Feller 1941).
4. The limit $Q$, and the case $\mu_r = \infty$, where $e^{-rt} B(t) \to 0$, as a separate statement.

## Sources

- J. H. Jones, Population growth in continuous time, Formal Demography Workshop lecture notes, Stanford University, 2008, eqs. (1)–(4).
- Renewal theory, Wikipedia, section Key renewal theorem. <https://en.wikipedia.org/wiki/Renewal_theory>
- Original result: W. Feller, On the integral equation of renewal theory, Ann. Math. Statist. 12 (1941), 243–267. <https://doi.org/10.1214/aoms/1177731708> The limit theorem follows the key renewal theorem in the renewal theory article and the model in Jones's notes.
- Original result: F. R. Sharpe and A. J. Lotka, A problem in age-distribution, Philos. Mag. 21 (1911), 435–438. <https://doi.org/10.1080/14786440408637050> The renewal model follows Jones's notes and the Euler–Lotka equation article.
- Euler–Lotka equation, Wikipedia, section Lotka's continuous model. <https://en.wikipedia.org/wiki/Euler%E2%80%93Lotka_equation>
