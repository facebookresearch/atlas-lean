# Caputo derivative and Matignon's stability criterion

**Caputo derivative.** For $n - 1 < \vartheta < n$ with $n \in \mathbb N$ and a function $\varphi : [0, \infty) \to \mathbb R$ whose $n$-th derivative is locally integrable, the Caputo derivative of order $\vartheta$ is

$$ {}^{C}_{0}D^{\vartheta}_t \varphi(t) = \frac{1}{\Gamma(n - \vartheta)} \int_0^t (t - \tau)^{n - \vartheta - 1}\, \varphi^{(n)}(\tau)\, d\tau ,$$

and ${}^{C}_{0}D^{n}_t\varphi = \varphi^{(n)}$. Basic properties:

- ${}^{C}_{0}D^{\vartheta}_t c = 0$ for a constant $c$;
- for $\varepsilon \ge 0$ an integer with $\varepsilon < \lceil \vartheta \rceil$, ${}^{C}_{0}D^{\vartheta}_t t^{\varepsilon} = 0$; for $\varepsilon > \lfloor \vartheta \rfloor$ (integer or not), ${}^{C}_{0}D^{\vartheta}_t t^{\varepsilon} = \dfrac{\Gamma(\varepsilon + 1)}{\Gamma(\varepsilon - \vartheta + 1)}\, t^{\varepsilon - \vartheta}$;
- the Laplace transform is $\mathcal L\{ {}^{C}_{0}D^{\vartheta}_t \varphi \}(s) = s^{\vartheta}\hat\varphi(s) - \sum_{v=0}^{n-1} \varphi^{(v)}(0)\, s^{\vartheta - v - 1}$, so initial conditions are those of integer-order equations.

**Fractional-order compartmental model.** Replace $\dot x = f(x)$, $x \in \mathbb R^m$, by ${}^{C}_{0}D^{\vartheta}_t x = f(x)$ with $0 < \vartheta \le 1$ (for dimensional consistency each rate parameter is often raised to the power $\vartheta$). Equilibria are the same zeros of $f$ as for $\vartheta = 1$.

**Theorem (Matignon).** Let $0 < \vartheta \le 1$ and $x^*$ an equilibrium with Jacobian $J = Df(x^*)$. If every eigenvalue $\xi$ of $J$ satisfies

$$|\arg \xi| > \frac{\vartheta\pi}{2},$$

then $x^*$ is locally asymptotically stable; solutions of the linearisation decay like $t^{-\vartheta}$ (Mittag-Leffler decay) rather than exponentially. If some eigenvalue has $|\arg\xi| < \vartheta\pi/2$, $x^*$ is unstable.

**Consequence for the reproduction number.** Since $\vartheta\pi/2 \le \pi/2$, every eigenvalue with negative real part satisfies the condition. Hence, for a fractional compartmental model whose integer-order version has the threshold property "the disease-free equilibrium is stable iff all Jacobian eigenvalues have negative real part iff $R_0 < 1$", the disease-free equilibrium of the fractional model is locally asymptotically stable when $R_0 < 1$; when $R_0 > 1$ a real positive eigenvalue ($\arg \xi = 0$) makes it unstable. $R_0$ is computed from the same next-generation matrix as for $\vartheta = 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

For the linear system ${}^{C}_{0}D^{\vartheta}_t y = Jy$ with diagonalisable $J$, the Laplace transform gives $\hat y(s) = (s^{\vartheta}I - J)^{-1} s^{\vartheta-1}y(0)$, and each mode is $E_\vartheta(\xi t^{\vartheta})$, a Mittag-Leffler function. $E_\vartheta(\xi t^\vartheta) \to 0$ exactly when $|\arg \xi| > \vartheta\pi/2$, with algebraic tail $\sim -t^{-\vartheta}/(\xi\,\Gamma(1-\vartheta))$; when $|\arg\xi| < \vartheta\pi/2$ it grows like $\exp(\xi^{1/\vartheta} t)/\vartheta$. The stable region is therefore larger than the open left half plane for $\vartheta < 1$: memory can stabilise equilibria that are unstable foci of the integer-order model, but it cannot stabilise a real positive eigenvalue, so the $R_0 = 1$ threshold is inherited. For characteristic polynomials of degree up to three, fractional analogues of the Routh–Hurwitz conditions check the argument condition directly from the coefficients.

## Sources

- P. A. Naik, M. Yavuz, S. Qureshi, J. Zu, S. Townley, "Modeling and analysis of COVID-19 epidemics with treatment in fractional derivatives using real data from Pakistan", European Physical Journal Plus 135 (2020) 795, Section 2 (Definitions 2–4 and 7, Eqs. 1–4 and 8), Section 3 ($R_0$, Eq. 17; Theorem 3 with the argument condition Eq. 18; Lemma 2, fractional Routh–Hurwitz conditions, Eq. 24), <https://doi.org/10.1140/epjp/s13360-020-00819-5> (PMC7594999).
- P. Pandey, Y.-M. Chu, J. F. Gómez-Aguilar, H. Jahanshahi, A. A. Aly, "A novel fractional mathematical model of COVID-19 epidemic considering quarantine and latent time", Results in Physics 26 (2021) 104286, Section "Caputo fractional derivatives" (Eqs. 1–3, derivative of constants and powers), <https://doi.org/10.1016/j.rinp.2021.104286> (PMC8131186).
- D. Matignon, "Stability results for fractional differential equations with applications to control processing", Computational Engineering in Systems Applications 2 (1996) 963–968.
