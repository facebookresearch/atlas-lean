# Moment generating function of the gamma distribution

Let $a > 0$ and $r > 0$, and let $X$ have the gamma distribution with shape $a$ and rate $r$ (density $\frac{r^a}{\Gamma(a)} x^{a-1} e^{-rx}$ for $x \ge 0$, and $0$ for $x < 0$). For every real $t < r$, the moment generating function of $X$ at $t$ is $\mathbb{E}[e^{tX}] = \left(\frac{r}{r - t}\right)^a$.

## Idea

Multiplying the gamma density by $e^{tx}$ replaces the rate $r$ by $r - t$. As long as $r - t > 0$ the result is again a gamma integrand, whose integral is known, and the ratio of normalising constants is $(r/(r - t))^a$. For $t \ge r$ the integral diverges: exponential moments are finite exactly below the rate. Because the moment generating function is finite on a neighbourhood of $0$, it determines the law, so a probability measure with the same moment generating function is this gamma law. Products then identify sums: independent gamma variables with a common rate add their shapes, which covers Erlang and chi-square laws.

## Statements

- [Moment generating function of the gamma distribution](mgf-gamma-measure-of-lt.md)
- [Exponential moments of the gamma distribution](integrable-exp-mul-gamma-measure.md): lemma used in the proof of the main statement
- [Half-line of exponential integrability for the gamma distribution](iio-subset-integrable-exp-set-gamma-meas.md): lemma: exponential moments below the rate
- [Exponential moments of the gamma law are finite exactly below the rate](integrable-exp-set-gamma-measure.md): exact range of exponential moments
- [A neighbourhood of zero of exponential integrability for the gamma distribution](ioo-subset-interior-integrable-exp-set-g.md): lemma: the moment generating function is finite near $0$
- [Moment generating function determines the gamma law](eq-gamma-measure-of-mgf-eq.md): uniqueness: the mgf determines the law
- [Laplace transform of the gamma density](lintegral-gamma-pdf-mul-exp.md): the moment generating function at $-c \le 0$, as an integral against the density
