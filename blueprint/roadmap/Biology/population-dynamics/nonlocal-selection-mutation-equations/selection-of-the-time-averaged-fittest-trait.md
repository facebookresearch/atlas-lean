# Selection of the trait with the largest time-averaged growth rate

Let $a(t,x)$ be $T$-periodic in $t$, bounded, and $C^3$ in $x \in \mathbb R^d$, with time average $\bar a(x) = \frac1T\int_0^T a(t,x)\,dt$ attaining its maximum at a unique point $x_m$ with $\bar a(x_m) > 0$, and let $0 \le n_0(x) \le e^{C_1 - C_2|x|}$ with positive initial mass, $\int_{\mathbb R^d} n_0\,dx > 0$. Consider

$$\partial_t n - \sigma\Delta n = n\,[a(t,x) - \rho(t)], \qquad \rho(t) = \int_{\mathbb R^d} n(t,x)\,dx, \qquad n(0,\cdot) = n_0.$$

**No mutation ($\sigma = 0$).** Assume further that the Hessian of $\bar a$ at $x_m$ is negative definite, that $a \le -\delta < 0$ for $|x| \ge R_0$, that $n_0, a$ are bounded in $W^{3,\infty}$, and that $n_0$ has mass in every neighbourhood of the maximizer: $\int_{|x - x_m| < r} n_0\,dx > 0$ for every $r > 0$ (for instance, $n_0$ continuous with $n_0(x_m) > 0$). Then $\|\rho(t) - \tilde\varrho(t)\|_{L^\infty} \to 0$, where $\tilde\varrho$ is the positive periodic solution of $\tilde\varrho' = \tilde\varrho\,(a(t,x_m) - \tilde\varrho)$, and $n(t,\cdot)/\rho(t) \rightharpoonup \delta_{x_m}$ weakly as measures. The trait with the largest *time-averaged* growth rate is selected, while the population size keeps oscillating. The condition near $x_m$ cannot be dropped: with $\sigma = 0$ the equation multiplies $n_0$ pointwise by a positive factor, so a datum vanishing on a neighbourhood of $x_m$ vanishes there for all time, and its normalization cannot converge to $\delta_{x_m}$.

**With mutation ($\sigma > 0$).** Let $(\lambda, p)$ be the principal eigenpair of the periodic parabolic problem $\partial_t p - \sigma\Delta p - a(t,x)p = \lambda p$, $p > 0$ and $T$-periodic, and assume $a(t,x) + \lambda \le -\delta < 0$ for $|x| \ge R_0$. Define the periodic functions $P(t,x) = p/\int p\,dx$ and $Q(t) = \int a\,p\,dx / \int p\,dx$. Then:
1. if $\lambda \ge 0$, $\rho(t) \to 0$ (extinction);
2. if $\lambda < 0$ (and, as assumed, $\int n_0\,dx > 0$), $|\rho(t) - \tilde\rho(t)| \to 0$, where $\tilde\rho$ is the positive periodic solution of $\tilde\rho' = \tilde\rho\,(Q(t) - \tilde\rho)$, and $\|n(t,\cdot) - \tilde\rho(t)P(t,\cdot)\|_{L^\infty} \to 0$.
For $\sigma$ small enough, $\lambda < 0$.

## Depends on

- [Periodic logistic equation](periodic-logistic-equation.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

With $\sigma = 0$, $N = n\,e^{\int_0^t\rho}$ solves the linear equation $\partial_t N = aN$, so by Floquet theory $N(t,x) = e^{\bar a(x)t}p_0(t,x)$ with $p_0$ periodic in $t$; the normalized density therefore concentrates where $\bar a$ is maximal, by Laplace's method around the non-degenerate maximum $x_m$. Integrating the equation in $x$ gives $\rho' = \rho\,(\int a\,n/\rho\,dx - \rho)$, and the mean fitness $\int a\,n/\rho$ tends to $a(t,x_m)$, reducing $\rho$ to an asymptotically periodic logistic equation. With mutation, $\lambda < 0$ means the periodic linearized problem grows; dividing $n$ by $\rho$ the profile converges to the normalized principal eigenfunction $P$, and $\int a\,P = Q$ plays the role of $a(t,x_m)$. The periodic solution has time average $\frac1T\int_0^T\tilde\rho = \frac1T\int_0^T Q = -\lambda$.

## Sources

- S. Figueroa Iglesias and S. Mirrahimi, "Long time evolutionary dynamics of phenotypically structured populations in time-periodic environments", SIAM Journal on Mathematical Analysis (2018), Section 1.3 (Proposition 1, Equations 3–4; Proposition 2, Equations 5–8; Theorem 4, Equations 9–13), Section 1.4 (Equations 14–16) and Section 2, <https://doi.org/10.1137/18M1175185>.
