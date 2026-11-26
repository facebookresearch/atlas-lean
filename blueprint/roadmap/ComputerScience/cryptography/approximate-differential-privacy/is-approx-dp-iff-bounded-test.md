# Approximate differential privacy via bounded tests

A mechanism $M$ with values in probability mass functions is [$(\varepsilon, \delta)$-differentially private](is-approx-dp.md) for $\mathrm{adj}$ if and only if $\varepsilon \ge 0$, $\delta \ge 0$, and for every ordered pair with $\mathrm{adj}(d, d')$ and every test $f$ from outputs to $[0, 1]$ (valued in the extended nonnegative reals with $f(a) \le 1$),

$$
\sum_a M(d)(a)\, f(a) \le e^{\varepsilon} \sum_a M(d')(a)\, f(a) + \delta .
$$

The additive $\delta$ appears once, outside the whole expectation.
