# Caputo fractional derivative

**Definition.** Let $\vartheta > 0$ and $n = \lceil \vartheta \rceil$. For a function $\varphi : [0, \infty) \to \mathbb R$ whose $n$-th derivative is locally integrable, the Caputo derivative of order $\vartheta$ is, when $n - 1 < \vartheta < n$,

$${}^{C}_{0}D^{\vartheta}_t \varphi(t) = \frac{1}{\Gamma(n - \vartheta)} \int_0^t (t - \tau)^{n - \vartheta - 1}\, \varphi^{(n)}(\tau)\, d\tau , \qquad t > 0,$$

and, when $\vartheta = n$ is an integer, the ordinary derivative ${}^{C}_{0}D^{n}_t\varphi = \varphi^{(n)}$. For $0 < \vartheta < 1$ this reads ${}^{C}_{0}D^{\vartheta}_t \varphi(t) = \Gamma(1 - \vartheta)^{-1} \int_0^t (t - \tau)^{-\vartheta} \varphi'(\tau)\, d\tau$, a convolution of $\varphi'$ with a power-law memory kernel, and ${}^{C}_{0}D^{1}_t \varphi = \varphi'$.

**Properties.** For $n - 1 < \vartheta < n$:

- ${}^{C}_{0}D^{\vartheta}_t c = 0$ for a constant $c$;
- for an integer $\varepsilon$ with $0 \le \varepsilon < n$, ${}^{C}_{0}D^{\vartheta}_t t^{\varepsilon} = 0$; for real $\varepsilon > n - 1$, ${}^{C}_{0}D^{\vartheta}_t t^{\varepsilon} = \dfrac{\Gamma(\varepsilon + 1)}{\Gamma(\varepsilon - \vartheta + 1)}\, t^{\varepsilon - \vartheta}$;
- the Laplace transform is $\mathcal L\{ {}^{C}_{0}D^{\vartheta}_t \varphi \}(s) = s^{\vartheta}\hat\varphi(s) - \sum_{v=0}^{n-1} \varphi^{(v)}(0)\, s^{\vartheta - v - 1}$, so initial conditions are those of integer-order equations.

A **Caputo fractional-order compartmental model** replaces $\dot x = f(x)$, $x \in \mathbb R^m$, by ${}^{C}_{0}D^{\vartheta}_t x = f(x)$ with $0 < \vartheta \le 1$; for dimensional consistency each rate parameter $\kappa$ is often written $\kappa^{\vartheta}$, keeping both sides in units of $(\text{time})^{-\vartheta}$. Since the derivative annihilates constants, its equilibria are the zeros of $f$, as for $\vartheta = 1$.

## Expansion

The power rule follows by substituting $\tau = t u$ and using the Beta integral; integer powers below $n$ vanish because their $n$-th derivative does. As $\vartheta \uparrow n$ the kernel $(t-\tau)^{n-\vartheta-1}/\Gamma(n-\vartheta)$ concentrates at $\tau = t$, so for $\varphi \in C^n$ the Caputo derivative tends to $\varphi^{(n)}(t)$, consistent with the integer case of the definition; the integral itself is not used at $\vartheta = n$, where $\Gamma(0)$ is undefined and the kernel is not integrable. Unlike the Riemann–Liouville derivative, the Caputo derivative needs only the integer-order initial values $\varphi^{(v)}(0)$, which is why it is used for compartmental models. An example is the SEIQR model ${}^{C}D^{\vartheta}_t S = \Lambda^{\vartheta} - \mu^{\vartheta} S - \beta^{\vartheta} S (E + I)$, ${}^{C}D^{\vartheta}_t E = \beta^{\vartheta} S (E + I) - (\pi^{\vartheta} + \mu^{\vartheta} + \gamma^{\vartheta}) E$, ${}^{C}D^{\vartheta}_t I = \pi^{\vartheta} E - (\sigma^{\vartheta} + \mu^{\vartheta}) I$, ${}^{C}D^{\vartheta}_t Q = \gamma^{\vartheta} E + \sigma^{\vartheta} I - (\theta^{\vartheta} + \mu^{\vartheta}) Q$, ${}^{C}D^{\vartheta}_t R = \theta^{\vartheta} Q - \mu^{\vartheta} R$.

## Sources

- K. Diethelm, *The Analysis of Fractional Differential Equations*, Lecture Notes in Mathematics 2004, Springer (2010), Chapter 3, <https://doi.org/10.1007/978-3-642-14574-2>.
- P. A. Naik, M. Yavuz, S. Qureshi, J. Zu, S. Townley, "Modeling and analysis of COVID-19 epidemics with treatment in fractional derivatives using real data from Pakistan", European Physical Journal Plus 135 (2020) 795, Section 2 (Definitions 2–4 and 7, Eqs. 1–4 and 8), <https://doi.org/10.1140/epjp/s13360-020-00819-5> (PMC7594999).
- P. Pandey, Y.-M. Chu, J. F. Gómez-Aguilar, H. Jahanshahi, A. A. Aly, "A novel fractional mathematical model of COVID-19 epidemic considering quarantine and latent time", Results in Physics 26 (2021) 104286, Section "Caputo fractional derivatives" (Eqs. 1–3, derivative of constants and powers), <https://doi.org/10.1016/j.rinp.2021.104286> (PMC8131186).
- Z. Zhang, A. Zeb, O. F. Egbelowo, V. S. Erturk, "Dynamics of a fractional order mathematical model for COVID-19 epidemic", Advances in Difference Equations 2020 (2020) 420, model (3), <https://doi.org/10.1186/s13662-020-02873-w> (PMC7427275).
