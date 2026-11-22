# Moments of the gamma distribution

Let $a > 0$ and $r > 0$, and let $\mathrm{Gamma}(a, r)$ be the gamma law with shape $a$ and rate $r$, the probability measure on $\mathbb{R}$ with density $\frac{r^a}{\Gamma(a)} x^{a-1} e^{-rx}$ for $x \ge 0$ and $0$ for $x < 0$. For every real $p > -a$, $\int x^p \, d\mathrm{Gamma}(a, r)(x) = \Gamma(a + p) / (\Gamma(a)\, r^p)$. Here $x^p$ is the real power; the law is carried by $[0, \infty)$ and gives $\{0\}$ measure zero, so the values of $x^p$ for $x \le 0$ play no role.

## Idea

Multiplying the gamma density by $x^p$ gives another gamma integrand, with shape $a + p$. The substitution $y = rx$ turns the integral into $\Gamma(a + p)$ times powers of $r$, which yields the formula. The condition $p > -a$ is exactly integrability near $0$, so negative moments are included: for $a > 1$, $\mathbb{E}[1/X] = r/(a - 1)$. The cases $p = 1$ and $p = 2$ give the mean $a/r$ and the second moment $a(a + 1)/r^2$, hence the variance $a/r^2$. The rate is an inverse scale parameter: if $X$ has law $\mathrm{Gamma}(a, r)$ then $cX$ has law $\mathrm{Gamma}(a, r/c)$ for $c > 0$, which explains the factor $r^{-p}$.

## Statements

- [Real moments of the gamma law](integral-rpow-gamma-measure.md)
- [Gamma law is concentrated on the nonnegative reals](ae-nonneg-gamma-measure.md): basic property: support in $[0, \infty)$
- [$r^k r^{a-1} = r^{a+k-1}$ for nonnegative $r$](pow-mul-rpow-sub-one.md): algebraic lemma used for the integrals
- [Gamma function at $a + k$ via the rising factorial](gamma-add-nat-eq.md): gamma-function identity linking $\Gamma(a + k)$ to the rising factorial that appears in the integer gamma integrals
- [Integrability of the scaled gamma integrand](integrable-on-rpow-mul-exp-neg-mul-ioi.md): lemma: integrability of the gamma integrand
- [Integrability of $x^k e^{-cx}$ under the gamma law](integrable-pow-mul-exp-neg-mul-gamma-mea.md): lemma: integrability of $x^k e^{-cx}$
- [Gamma integrals](integral-pow-mul-exp-neg-mul-gamma-measu.md): gamma integrals against the law, a variant of the main formula
- [Gamma law has finite first moment](integrable-id-gamma-measure.md): special case: the first moment is finite
- [Gamma law has finite second moment](integrable-sq-gamma-measure.md): special case: the second moment is finite
- [Gamma law has finite second moment](mem-lp-id-gamma-measure.md): special case: the identity is square integrable
- [Mean of the gamma law](integral-id-gamma-measure.md): special case: the mean
- [Second moment of the gamma law](integral-sq-gamma-measure.md): special case: second moment
- [Variance of the gamma law](variance-id-gamma-measure.md): consequence: the variance $a/r^2$
- [Real moments of the gamma density](lintegral-gamma-pdf-mul-rpow.md): the main formula as an integral against the density
- [Euler's gamma integral](lintegral-rpow-mul-exp-neg-mul-ioi.md): the normalising integral of the gamma density
