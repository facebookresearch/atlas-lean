# Sharpe–Lotka–Feller renewal theorem for births

In Lotka's renewal model the births $B(t)$ at time $t$ are the births $G(t)$ to women alive at time $0$ plus the births to women born since, $B(t) = G(t) + \int_0^t B(t - a)\, \varphi(a)\, da$, where $\varphi(a) = l(a) m(a)$ is the net maternity function, $l$ the survivorship and $m$ the age-specific fertility (the model of Sharpe and Lotka 1911, treated rigorously by Feller 1941). Let $\varphi \ge 0$ be measurable with $\int_0^\infty \varphi > 0$, let $r$ be the real root of the characteristic equation $\int_0^\infty e^{-ra}\varphi(a)\, da = 1$ (Feller 1971, Section XI.6, equation (6.10), with $r = -\kappa$), and assume $\mu_r = \int_0^\infty a\, e^{-ra}\varphi(a)\, da < \infty$. Let $G \ge 0$ be such that $t \mapsto e^{-rt}G(t)$ is integrable on $[0, \infty)$ and non-increasing, and let $B$ be the solution of the renewal equation that is bounded on compact sets. Then

$$e^{-rt} B(t) \to Q = \frac{1}{\mu_r}\int_0^\infty e^{-rt} G(t)\, dt \qquad (t \to \infty),$$

so births ultimately grow like $Q e^{rt}$. A nonzero exponential $c\,e^{rt}$ does not solve the homogeneous half-line equation ($G = 0$): at $t = 0$ that equation forces $B(0) = 0$. The exponentials solve instead the full-history equation $B(t) = \int_0^\infty B(t - a)\,\varphi(a)\,da$ for every real $t$, and these solutions are characterized by the [renewal equation for exponential growth](../../../epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff.md). On the half-line, $c\,e^{rt}$ solves the renewal equation above with the inherited forcing $G(t) = c\,e^{rt}\int_t^\infty e^{-ra}\varphi(a)\,da$, the births to women born before time $0$ in a population that has always grown at rate $r$; this $G$ satisfies the hypotheses of the theorem and gives $Q = c$. The theorem shows that every solution of the half-line equation with $G$ as above is asymptotic to $Q e^{rt}$.

The derivation is explicit. Put $B_r(t) = e^{-rt}B(t)$, $G_r(t) = e^{-rt}G(t)$ and $f(a) = e^{-ra}\varphi(a)$. Multiplying the renewal equation by $e^{-rt}$ gives $B_r = G_r + B_r * f$, and $f$ is a probability density with mean $\mu_r$. Hence $B_r(t) = G_r(t) + \int_0^t G_r(t - x)\, u(x)\, dx$ with $u = \sum_{n \ge 1} f^{*n}$ the renewal density of the renewal process with inter-renewal density $f$, and the renewal theorem in its alternative form for directly Riemann integrable functions, applied to the nonarithmetic distribution with density $f$ (Feller 1971, Section XI.1; a non-increasing integrable function is directly Riemann integrable), gives $\int_0^t G_r(t - x) u(x)\, dx \to \mu_r^{-1}\int_0^\infty G_r$, while $G_r(t) \to 0$ because $G_r$ is non-increasing and integrable.

## Depends on

- [Renewal equation for exponential growth](../../../epidemiology/euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff.md)

## Expansion

1. The model: the renewal equation for births with the initial-population term $G$, and existence and uniqueness of its solution bounded on compact sets.
2. The reduction by the factor $e^{-rt}$ to a renewal equation with a probability density $f$, and the representation of its solution through the renewal density $u$.
3. The key renewal theorem in the form used here, and its extension to directly Riemann integrable $G_r$ (Feller 1971, Section XI.1).
4. The limit $Q$, and the case $\mu_r = \infty$, where $e^{-rt} B(t) \to 0$, as a separate statement.

## Sources

- Original result: W. Feller, On the integral equation of renewal theory, Ann. Math. Statist. 12 (1941), 243–267. <https://doi.org/10.1214/aoms/1177731708>
- W. Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed., Wiley, New York, 1971, Section XI.1 (the lemma on the solution bounded on finite intervals, and the renewal theorem, alternative form, for directly Riemann integrable functions) and Section XI.6 (the reduction by an exponential factor, equations (6.10)–(6.14), including the case of total mass greater than $1$).
- Original result: F. R. Sharpe and A. J. Lotka, A problem in age-distribution, Philos. Mag. 21 (1911), 435–438. <https://doi.org/10.1080/14786440408637050>
