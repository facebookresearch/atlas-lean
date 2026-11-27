# Expected number of internal equilibria in random multi-player two-strategy games

**Setting.** In a $d$-player game with two strategies, let $\beta_k$ be the payoff to strategy 1 minus the payoff to strategy 2 for a focal player whose $d-1$ co-players include $k$ strategists of type 1. Under replicator dynamics in a well-mixed population with frequency $y \in (0,1)$ of strategy 1, the internal equilibria are the roots in $(0,1)$ of the random Bernstein polynomial

$$\sum_{k=0}^{d-1}\beta_k\binom{d-1}{k}y^k(1-y)^{d-1-k} = 0, \qquad\text{equivalently}\qquad \sum_{k=0}^{d-1}\beta_k\binom{d-1}{k}t^k = 0,\ \ t = \frac{y}{1-y} \in (0,\infty).$$

Take the payoff differences $\beta_k$ i.i.d. centered Gaussian. Let $f_d(t)$ be the expected density of positive real roots (Kac–Rice) and $E(2,d) = \int_0^\infty f_d(t)\,dt$ the expected number of internal equilibria.

**Properties of the density.** With $M_d(t) = \sum_{k=0}^{d-1}\binom{d-1}{k}^2 t^{2k}$:

$$f_d(t) = \frac{1}{2\pi}\Big[\frac1t\frac{d}{dt}\Big(t\frac{d}{dt}\log M_d(t)\Big)\Big]^{1/2}, \qquad f_d(0) = \frac{d-1}{\pi}, \qquad f_d(1) = \frac{d-1}{2\pi\sqrt{2d-3}},$$

$f_d$ is decreasing, $f_d(1/t) = t^2 f_d(t)$, and $E(2,d) = 2\int_0^1 f_d$. In the frequency variable the density $g_d(y) = f_d\big(\frac{y}{1-y}\big)(1-y)^{-2}$ is symmetric, $g_d(y) = g_d(1-y)$.

**Theorem.**

1. $f_d(t) \le \min\Big\{\dfrac{\sqrt{d-1}}{2\pi t},\ \dfrac{d-1}{\pi}\Big\}$ for $t \ge 0$.
2. $\sqrt{d-1} \lesssim E(2,d) \lesssim \sqrt{d-1}\,\ln(d-1)$, and

    $$\lim_{d\to\infty}\frac{\ln E(2,d)}{\ln(d-1)} = \frac12.$$

For $d \ge 3$ the explicit bounds $\frac{d-1}{\pi\sqrt{2d-3}} = 2f_d(1) \le E(2,d) \le \frac{\sqrt{d-1}}{\pi}\big(1 + \ln 2 + \tfrac12\ln(d-1)\big)$ are the case $\alpha = 0$, $n = d-1$ of [Expected number of real roots of random polynomials from multiplayer games](expected-number-of-real-roots-of-random-polynomials-from-multiplayer-games.md), since $E(2,d)$ is half the expected number of real roots of $\sum_k \beta_k\binom{d-1}{k}t^k$; the stability count $SE(2,d) = E(2,d)/2$ is on [Expected number of internal equilibria in random multi-player multi-strategy games](expected-number-of-internal-equilibria-in-random-multi-player-multi-strategy-games.md).

So, although a $d$-player game can have up to $d-1$ internal equilibria, a random one has only of order $\sqrt d$ of them up to a logarithm; the same bound counts real zeros in $(0,1)$ of a random Bernstein polynomial of degree $d-1$.

## Depends on

- [Expected number of internal equilibria in random multi-player multi-strategy games](expected-number-of-internal-equilibria-in-random-multi-player-multi-strategy-games.md)
- [Expected number of real roots of random polynomials from multiplayer games](expected-number-of-real-roots-of-random-polynomials-from-multiplayer-games.md)

## Expansion

The Kac–Rice formula gives the root density of a Gaussian polynomial with covariance kernel $M_d(\sqrt{st})$ as $\frac{1}{\pi}\sqrt{\partial_s\partial_t \log K(s,t)}$ on the diagonal, which yields the $M_d$ formula. Writing $M_d(t) = \prod_i (t^2 + r_i)$ gives $(2\pi f_d)^2 = \sum_i 4r_i/(t^2 + r_i)^2$, from which both bounds in part 1 follow. Splitting $E(2,d) = 2\int_0^1 f_d$ at $\alpha = 1/(2\sqrt{d-1})$, using $f_d(0)$ below $\alpha$ and the $\sqrt{d-1}/(2\pi t)$ bound above, gives the upper bound; monotonicity gives the lower bound $2f_d(1)$.

## Sources

- Manh Hong Duong and The Anh Han, "Analysis of the expected density of internal equilibria in random evolutionary multi-player multi-strategy games", Journal of Mathematical Biology 73 (2016), 1727–1760, <https://doi.org/10.1007/s00285-016-1010-8>; numbering as in arXiv:1505.04676: section "Multi-player two-strategy games" (properties of $f_{2,d}$, symmetry lemma, "Asymptotic behaviour of the density function", "Asymptotic behaviour of $E(2,d)$" and the stable-equilibrium and Bernstein-polynomial corollaries).
