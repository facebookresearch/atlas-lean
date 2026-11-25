# Moments of the exponential distribution

Let $r > 0$ and let $\operatorname{Exp}(r)$ be the exponential law with rate $r$, the probability measure on $\mathbb{R}$ with density $r e^{-rx}$ for $x \ge 0$ and $0$ for $x < 0$. For every natural number $n$, its $n$-th moment is $\int x^n \, d\operatorname{Exp}(r)(x) = n!/r^n$.

## Idea

The exponential law is the law of a waiting time without memory, and the gamma law with shape $1$. Its moments come from one substitution: with $y = rx$, $\int_0^\infty x^n r e^{-rx}\, dx = r^{-n} \int_0^\infty y^n e^{-y}\, dy = n!/r^n$, the last integral being $\Gamma(n + 1)$. Every moment is finite because the exponential decay of the density beats any power. The first two cases give the mean $1/r$ and $\mathbb{E}[X^2] = 2/r^2$, hence the variance $1/r^2$: the standard deviation equals the mean. The same values hold for any random variable whose law is $\operatorname{Exp}(r)$.

## Statements

- [Moments of the exponential law](integral-pow-exp-measure.md)
- [Exponential density as an indicator on the half-line](gamma-pdfreal-one-eq-indicator.md): lemma: the density as an indicator times an exponential
- [Power times exponential density in gamma-integrand form](pow-eq-rpow-mul-exp.md): lemma used in the proof of the main statement
- [Integrals against the exponential law](integral-exp-measure-eq-set-integral.md): lemma used in the proof of the main statement
- [Integrability criterion for the exponential law](integrable-exp-measure-iff.md): integrability criterion, used for the moments
- [Finiteness of all moments of the exponential law](integrable-pow-exp-measure.md): basic property: every moment is finite
- [Integrability of the identity under the exponential law](integrable-id-exp-measure.md): special case: the first moment is finite
- [Mean of the exponential law](integral-id-exp-measure.md): special case: the mean
- [Second moment of the exponential law](integral-sq-exp-measure.md): special case: second moment
- [Variance of the exponential law](variance-id-exp-measure.md): consequence: the variance $1/r^2$
- [Exponentially distributed random variables are integrable](integrable-of-exp-measure.md): random-variable form
- [Mean of an exponentially distributed random variable](integral-eq-inv-of-exp-measure.md): random-variable form of the mean
- [Variance of an exponentially distributed random variable](variance-eq-of-exp-measure.md): random-variable form of the variance
- [Competing exponential clocks](competing-exponential-clocks.md)
- [The memoryless property characterizes the exponential law](memoryless-property-characterizes-the-exponential-law.md)
