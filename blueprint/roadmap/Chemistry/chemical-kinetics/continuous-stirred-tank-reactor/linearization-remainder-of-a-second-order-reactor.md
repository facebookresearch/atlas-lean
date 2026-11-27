# Exact linearization remainder for a second-order stirred tank

Let $D > 0$, $k > 0$ and $c_{\mathrm{in}} \ge 0$, and let $c^* > 0$ satisfy $D(c_{\mathrm{in}} - c^*) = k (c^*)^2$, the positive
equilibrium of the constant-density stirred tank with second-order reaction

$$c' = D(c_{\mathrm{in}} - c) - k c^2 .$$

Put $\delta = c - c^*$, $d = \delta(0)$, and $\lambda = D + 2 k c^*$. Then $\delta' = -\lambda\delta - k\delta^2$ exactly. If
$d > -\lambda/k$, the profile

$$\delta(t) = \frac{d\,e^{-\lambda t}}{1 + (kd/\lambda)\,(1 - e^{-\lambda t})}$$

has a positive denominator for all $t \ge 0$, starts at $d$, solves the deviation equation there, and tends to zero as
$t \to +\infty$. If additionally $|d| < \lambda/k$, its denominator is at least $1 - k|d|/\lambda > 0$, and
$|\delta(t)| \le |d|\,e^{-\lambda t}/(1 - k|d|/\lambda)$ for $t \ge 0$. This absolute-value margin is sufficient, not
necessary: every $d > 0$ also decays.

Physical states also need $c(0) = c^* + d \ge 0$. Since $\lambda/k = D/k + 2c^* > c^*$, every physical initial
state has $d > -\lambda/k$. The denominator vanishes at a finite nonnegative time exactly when
$d < -\lambda/k$, outside the physical initial states. This singularity is a boundary of the mathematical model,
not a predicted failure of a reactor.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.37, the constant-density stirred-tank balance (p. 128), here with production rate $-k c^2$. The remainder and the explicit solution are derived above (a Bernoulli equation).
