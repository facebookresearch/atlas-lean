# Positivity, boundedness and characteristic roots of the logistic delay epidemic equation

**Model.** Let $F(t)$ be the infected fraction ("level of infectiousness") with infection rate $\beta>0$ and a recovery term proportional to the infected level a fixed infectious period $\tau$ earlier, with rate $\gamma>0$:

$$F'(t) = F(t)\big\{\beta[1-F(t)] - \gamma F(t-\tau)\big\}, \qquad F = \Phi \text{ on } [-\tau,0].$$

Any nonzero limit must be $F_\infty = \beta/(\beta+\gamma)$. In units of $\tau$ and with $f = F/F_\infty$,

$$f'(t) = \tilde\beta f(t)\big\{1 - \beta^* f(t) - \gamma^* f(t-1)\big\},\qquad \tilde\beta = \beta\tau,\ \beta^* = \tfrac{\beta}{\beta+\gamma},\ \gamma^* = \tfrac{\gamma}{\beta+\gamma},$$

with continuous, positive initial history $\phi$ on $[-1,0]$.

**Theorem (well-posedness and bounds).** The solution exists for all $t \ge 0$, is positive, and satisfies

$$0 < f(t) < \frac{f_0}{\beta^* f_0 + (1-\beta^* f_0)e^{-\tilde\beta t}},\qquad t > 0,$$

so it is bounded (by about $1/\beta^*$ for large $t$); if $\lim_{t\to\infty} f(t)$ exists it equals $1$.

**Theorem (characteristic roots).** Linearizing at $f = 1$ gives the characteristic function $h(s) = s + b\,[1 + \rho e^{-s}]$ with $b = \tilde\beta\beta^*$ and $\rho = \gamma/\beta$; let $B = \rho b e^{b}$. Then:
1. all zeros of $h$ are simple;
2. all zeros lie to the left of some vertical line $\operatorname{Re} s = p$;
3. if $B > 1$ there is a decreasing unbounded sequence of real parts $x_n$ with complex zeros $s_n = x_n \pm i\,k(x_n)$, which produce oscillatory (undulating) modes; the real part $x_M$ of the turning point of the root curve is positive iff $\rho > 1$, i.e. $\gamma > \beta$.

**Decay.** If the rightmost real part $x_0$ is negative and $c = \rho b e^{b}$ in the source's notation satisfies $c < \pi$, solutions of the linearized equation decay to $0$ uniformly and exponentially, and for the forced linear equation $f(t) - f_{[0]} \to 0$ whenever the forcing has a limit. When the dominant roots cross into the right half-plane, the nonlinear equation can instead show sustained oscillations (limit cycles).

## Expansion

Writing $g = 1/f$ turns the equation into a Bernoulli-type linear delay equation for $g$ that can be solved step by step on $[0,1), [1,2), \ldots$ by an integrating factor, which proves positivity; dropping the nonnegative delayed recovery term yields a logistic comparison equation and hence the upper bound. The delay term is what makes the dynamics oscillatory: the linearized equation $\varepsilon' = -b(\varepsilon(t) + \rho\,\varepsilon(t-1))$ is the classical Hayes-type equation, whose infinitely many complex characteristic roots are located along the curve $k(x)$ obtained by separating real and imaginary parts of $h(x+iy)=0$, giving estimates such as $\log\frac{e^{-(b+1)}}{(n+1)\pi} < x_n < \log\frac{c}{n\pi}$ for the higher roots.

## Sources

- Niko Sauer, "Epidemics: towards understanding undulation and decay", Afrika Matematika 36 (2025), 100, <https://doi.org/10.1007/s13370-025-01318-5>; numbering as in arXiv:2206.03133: equations (Normal) and (expr1), Theorems 4.1, 4.2, 6.1, 8.1, 8.2 and 9.1, Corollary 8.1.
