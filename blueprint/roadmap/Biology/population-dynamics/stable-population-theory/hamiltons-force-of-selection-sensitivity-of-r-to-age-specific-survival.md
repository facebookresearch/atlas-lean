# Hamilton's force of selection on age-specific survival

Consider continuous age $x$ with mortality rate $\mu(x)$, survivorship $l(x) = \exp(-\int_0^x \mu)$, maternity function $m(x)$, population growth rate $r$ given by the Euler–Lotka equation $\int_0^\infty e^{-ra} l(a) m(a)\, da = 1$, and generation time $\bar A = \int_0^\infty a\, e^{-ra} l(a) m(a)\, da > 0$. Implicit differentiation of the Euler–Lotka equation gives Hamilton's sensitivities (Caswell 2019, eqs. (3.11) and (3.22)):

$$\frac{dr}{d\mu(x)} = -\frac{1}{\bar A}\int_x^\infty e^{-ra} l(a) m(a)\, da, \qquad \frac{dr}{dm(x)} = \frac{e^{-rx} l(x)}{\bar A},$$

where $dr/d\mu(x)$ is the response of $r$ to a unit impulse of mortality at age $x$. The magnitude $|dr/d\mu(x)|$ equals $1/\bar A$ for every age $x$ before the first age at which $m > 0$, is non-increasing in $x$, and decreases strictly on every interval where $e^{-ra} l(a) m(a)$ is not almost everywhere zero: the force of selection on survival declines with age once reproduction has begun (Hamilton 1966, as presented by Caswell 2019, Sec. 3.2).

## Expansion

1. The model: survivorship, maternity, the Euler–Lotka equation and the existence and uniqueness of its real root $r$.
2. Differentiability of $r$ under perturbations of $\mu$ and $m$ by the implicit function theorem, using $\bar A > 0$.
3. The two sensitivity formulas, with the perturbation of mortality at one age as a unit impulse (Caswell, eqs. (3.16)–(3.22)), and their forms in terms of the stable age distribution and reproductive value (eqs. (3.7)–(3.8)).
4. Monotonicity in $x$: the constant value before maturity and the strict decrease where reproduction occurs, read off from the first formula.
5. The discrete-age version for life tables with survival probabilities $p_a$, as a separate statement.

## Sources

- H. Caswell, *Sensitivity Analysis: Matrix Methods in Demography and Ecology*, Springer, 2019, Sec. 3.2, eqs. (3.1)–(3.22). <https://doi.org/10.1007/978-3-030-10534-1>
- Original result: W. D. Hamilton, The moulding of senescence by natural selection, J. Theor. Biol. 12 (1966), 12–45. <https://doi.org/10.1016/0022-5193(66)90184-6> The sensitivity formulas follow Caswell (2019), Sec. 3.2.
