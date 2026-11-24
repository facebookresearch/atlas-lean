# The Erlang C formula for a real number of servers

For $0 < a < s$ let $C(s, a) = \Big(\int_0^\infty (1+t)^s \frac{at}{1+t}e^{-at}\,dt\Big)^{-1}$. (i) For an integer $s = n$, $C(n, a)$ is the Erlang-C delay probability $\frac{a^n}{n!(1-\rho)}\Big(\sum_{k=0}^{n-1}\frac{a^k}{k!} + \frac{a^n}{n!(1-\rho)}\Big)^{-1}$ of the M/M/$n$ queue with offered load $a$ and $\rho = a/n$. (ii) For fixed $a$, $C(s, a)$ is strictly decreasing in $s > a$. (iii) (Halfin and Whitt.) For every $\beta > 0$, $C(a + \beta\sqrt a, a) \to \theta(\beta) = \big(1 + \beta\Phi(\beta)/\varphi(\beta)\big)^{-1}$ as $a \to \infty$, with $\Phi$ and $\varphi$ the standard normal distribution and density functions; moreover $C(a + \beta\sqrt a, a)$ is strictly decreasing in $a$, so it exceeds $\theta(\beta)$ for every $a > 0$.

Proof of (i) and (ii). With $J(m) = \int_0^\infty (1+t)^m a e^{-at}\,dt = \frac{m!}{a^m}\sum_{j=0}^{m}\frac{a^j}{j!}$ and $t = (1+t) - 1$, the integral equals $J(n) - J(n-1) = \frac{n!}{a^n}\Big((1-\rho)\sum_{j<n}\frac{a^j}{j!} + \frac{a^n}{n!}\Big)$, the reciprocal of the Erlang-C value. For (ii), the integrand $(1+t)^{s-1}ate^{-at}$ increases strictly in $s$ for every $t > 0$.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Halfin–Whitt limit: $C(a + \beta\sqrt a, a) \to \big(1 + \beta\Phi(\beta)/\varphi(\beta)\big)^{-1}$ as $a \to \infty$ for every $\beta > 0$.
- Strict decrease of $C(a + \beta\sqrt a, a)$ in $a$ for fixed $\beta > 0$, via the stochastic ordering of $Y_a = (1 + X_a)^{\sqrt a}$ where $X_a$ has density $a t e^{-at}(1+t)^{a-1}$.

## Sources

- B. D'Auria, "A short note on the monotonicity of the Erlang C formula in the Halfin–Whitt regime", arXiv:1112.3689, 2011, <https://arxiv.org/abs/1112.3689>, equations (1)–(4) and Theorem 1 (rendered pages 1–2; the limit (4) is cited there to S. Halfin and W. Whitt, *Operations Research* 29, 1981)
