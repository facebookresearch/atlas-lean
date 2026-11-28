# The Erlang C formula for a real number of servers

For $0 < a < s$ let $C(s, a) = \Big(\int_0^\infty (1+t)^s \frac{at}{1+t}e^{-at}\,dt\Big)^{-1}$. (i) For an integer $s = n$, $C(n, a)$ is the Erlang-C delay probability $\frac{a^n}{n!(1-\rho)}\Big(\sum_{k=0}^{n-1}\frac{a^k}{k!} + \frac{a^n}{n!(1-\rho)}\Big)^{-1}$ of the M/M/$n$ queue with offered load $a$ and $\rho = a/n$. (ii) For fixed $a$, $C(s, a)$ is strictly decreasing in $s > a$. (iii) For fixed $\beta > 0$, $C(a + \beta\sqrt a, a)$ is strictly decreasing in $a > 0$. (iv) (Halfin and Whitt, 1981, in the form stated by D'Auria, 2011.) For every $\beta > 0$, $C(a + \beta\sqrt a, a) \to \theta(\beta) = \big(1 + \beta\Phi(\beta)/\varphi(\beta)\big)^{-1}$ as $a \to \infty$, with $\Phi$ and $\varphi$ the standard normal distribution and density functions; by (iii), $C(a + \beta\sqrt a, a) > \theta(\beta)$ for every $a > 0$.

Proof of (i)–(iii). With $J(m) = \int_0^\infty (1+t)^m a e^{-at}\,dt = \frac{m!}{a^m}\sum_{j=0}^{m}\frac{a^j}{j!}$ and $t = (1+t) - 1$, the integral equals $J(n) - J(n-1) = \frac{n!}{a^n}\Big((1-\rho)\sum_{j<n}\frac{a^j}{j!} + \frac{a^n}{n!}\Big)$, the reciprocal of the Erlang-C value. For (ii), the integrand $(1+t)^{s-1}ate^{-at}$ increases strictly in $s$ for every $t > 0$. For (iii), $g_a(t) = ate^{-at}(1+t)^{a-1}$ is a probability density on $(0, \infty)$, being the derivative of $-(1+t)^a e^{-at}$; if $X_a$ has density $g_a$ and $Y_a = (1 + X_a)^{\sqrt a}$, then $1/C(a + \beta\sqrt a, a) = E[Y_a^\beta]$ and $P(Y_a > y) = y^{\sqrt a}e^{-a(y^{1/\sqrt a} - 1)} = \exp\{(\log y)^2 h(\sqrt a/\log y)\}$ for $y > 1$, where $h(x) = x + x^2(1 - e^{1/x}) = -\sum_{n \ge 0} x^{-n}/(n+2)!$ is strictly increasing on $(0, \infty)$. So each tail probability increases strictly in $a$, and $E[Y_a^\beta] = 1 + \int_1^\infty \beta y^{\beta - 1}P(Y_a > y)\,dy$ increases strictly in $a$.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- For fixed $\beta > 0$, $E\big[(1 + X_a)^{\beta\sqrt a}\big] \to 1 + \beta\Phi(\beta)/\varphi(\beta)$ as $a \to \infty$, where $X_a$ has density $ate^{-at}(1+t)^{a-1}$ on $(0, \infty)$ (Laplace-method asymptotics of this integral).

## Sources

- B. D'Auria, "A short note on the monotonicity of the Erlang C formula in the Halfin–Whitt regime", arXiv:1112.3689, 2011, <https://arxiv.org/abs/1112.3689>, equations (1)–(4) and Theorem 1 with its proof (equations (5)–(7)); D'Auria attributes equation (4) to S. Halfin and W. Whitt, "Heavy-traffic limits for queues with many exponential servers", *Operations Research* 29 (1981)
