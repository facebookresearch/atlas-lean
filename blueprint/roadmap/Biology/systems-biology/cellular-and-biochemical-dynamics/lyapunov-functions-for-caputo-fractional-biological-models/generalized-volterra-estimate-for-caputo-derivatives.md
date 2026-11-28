# Generalized Volterra estimate for Caputo derivatives

**Setting.** For $0 < \alpha \le 1$ the Caputo derivative of a differentiable $x$ is ${}^C_{t_0}D^\alpha_t x(t) = \frac{1}{\Gamma(1-\alpha)}\int_{t_0}^t (t-s)^{-\alpha}x'(s)\,ds$ (the ordinary derivative when $\alpha = 1$). Many biological ODE models $\dot u = f(u)$ have Lyapunov functions of the form

$$V(u) = \sum_{i=1}^n a_i\Psi_i(u_i), \qquad \Psi_i(u_i) = \int_{u_i^*}^{u_i}\frac{g_i(s) - g_i(u_i^*)}{g_i(s)}\,ds = u_i - u_i^* - \int_{u_i^*}^{u_i}\frac{g_i(u_i^*)}{g_i(s)}\,ds,$$

with $a_i > 0$, $u^*$ a positive equilibrium and $g_i : \mathbb R_+ \to \mathbb R_+$ differentiable and strictly increasing; $g_i(s) = s$ gives the Volterra function $u_i - u_i^* - u_i^*\ln(u_i/u_i^*)$.

**Lemma.** Let $x(t) > 0$ be continuous and differentiable, $\bar x > 0$, $0 < \alpha \le 1$, and $g$ as above. Then for all $t \ge t_0$,

$${}^C_{t_0}D^\alpha_t\,\Psi(x(t)) \le \Big(1 - \frac{g(\bar x)}{g(x(t))}\Big)\,{}^C_{t_0}D^\alpha_t\,x(t), \qquad \Psi(x) = x - \bar x - \int_{\bar x}^x \frac{g(\bar x)}{g(s)}\,ds.$$

With $g(s) = s$ this is the known Volterra-type inequality ${}^C D^\alpha[x - \bar x - \bar x\ln(x/\bar x)] \le (1 - \bar x/x)\,{}^C D^\alpha x$.

**Proposition.** If $V = \sum_i a_i\Psi_i$ is a Lyapunov function for $\dot u = f(u)$, i.e. $\sum_i a_i\big(1 - g_i(u_i^*)/g_i(u_i)\big)f_i(u) \le 0$, then $V$ is also a Lyapunov function for the Caputo system ${}^C_{t_0}D^\alpha_t u = f(u)$: ${}^C_{t_0}D^\alpha_t V(u(t)) \le \sum_i a_i\big(1 - g_i(u_i^*)/g_i(u_i)\big)f_i(u) \le 0$. The same holds for quadratic Lyapunov functions $\sum_i \frac{c_i}{2}(u_i - u_i^*)^2$, using $\tfrac12{}^C D^\alpha(x - \bar x)^2 \le (x - \bar x)\,{}^C D^\alpha x$. With the fractional LaSalle principle, the integer-order global stability proof carries over verbatim; for instance, a fractional HIV model has a globally asymptotically stable disease-free equilibrium when $R_0 \le 1$ and a globally asymptotically stable endemic equilibrium when $R_0 > 1$, for every order $0 < \alpha \le 1$.

## Proof sketch

By linearity it suffices to show $\frac{g(\bar x)}{g(x(t))}\,{}^C D^\alpha x(t) \le {}^C D^\alpha\big[\int_{\bar x}^{x(t)} g(\bar x)/g(s)\,ds\big]$. Write both sides as integrals against the kernel $(t-s)^{-\alpha}$ and integrate by parts; the difference reduces to an integral of $(t-s)^{-\alpha-1}$ times

$$\int_{x(s)}^{x(t)}\Big(\frac{1}{g(\sigma)} - \frac{1}{g(x(t))}\Big)d\sigma,$$

which is non-negative for every $s$ because $1/g$ is decreasing: on the interval between $x(s)$ and $x(t)$, $1/g(\sigma) - 1/g(x(t))$ has the same sign as $x(t) - \sigma$. This is the convexity of $\Psi$ in disguise, since $\Psi''(x) = g(\bar x)g'(x)/g(x)^2 \ge 0$; Caputo derivatives of convex functions of $x$ are bounded by the chain-rule expression.

## Sources

- Adnane Boukhouima, Khalid Hattaf, El Mehdi Lotfi, Marouane Mahrouf, Delfim F.M. Torres and Noura Yousfi, "Lyapunov functions for fractional-order systems in biology: Methods and applications", *Chaos, Solitons & Fractals* 140 (2020), 110224, <https://doi.org/10.1016/j.chaos.2020.110224>. Preprint version: arXiv:2008.09177 (2020), main lemma on Caputo estimates with general $g$, its corollary, the propositions transferring Volterra and quadratic Lyapunov functions, and the global stability theorem for the fractional HIV model, <https://doi.org/10.48550/arXiv.2008.09177>.
