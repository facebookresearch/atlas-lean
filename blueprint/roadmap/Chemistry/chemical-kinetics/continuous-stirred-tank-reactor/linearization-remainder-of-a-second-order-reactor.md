# Exact linearization remainder for a second-order stirred tank

Let $D > 0$, $k > 0$ and $c_{\mathrm{in}} \ge 0$, and let $c^* > 0$ satisfy $D(c_{\mathrm{in}} - c^*) = k (c^*)^2$, the positive
equilibrium of the constant-density stirred tank with second-order reaction

$$c' = D(c_{\mathrm{in}} - c) - k c^2 .$$

Put $\delta = c - c^*$ and $\lambda = D + 2 k c^*$. Then $\delta' = -\lambda\delta - k\delta^2$ exactly. If
$\lvert\delta(0)\rvert < \lambda/k$, the solution

$$\delta(t) = \frac{\delta(0)\,e^{-\lambda t}}{1 + (k\delta(0)/\lambda)\,(1 - e^{-\lambda t})}$$

exists for all $t \ge 0$, its denominator is at least $1 - k\lvert\delta(0)\rvert/\lambda > 0$, and
$\lvert\delta(t)\rvert \le \lvert\delta(0)\rvert\,e^{-\lambda t}/(1 - k\lvert\delta(0)\rvert/\lambda)$. The margin
$\lvert\delta(0)\rvert < \lambda/k$ is sufficient, not necessary: every $\delta(0) > 0$ also decays.

Physical states also need $c(0) = c^* + \delta(0) \ge 0$. Since $\lambda/k = D/k + 2c^* > c^*$, every physical initial
state has $\delta(0) > -\lambda/k$, so the denominator never vanishes for physical data; it vanishes in finite time only
when $\delta(0) < -\lambda/k$, a negative initial concentration. That blow-up is a boundary of the mathematical model,
not a predicted failure of a reactor.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.37, the constant-density stirred-tank balance (p. 128), here with production rate $-k c^2$. The remainder and the explicit solution are derived above (a Bernoulli equation).
