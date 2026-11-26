# Chi-square distribution

For a natural number $p$, the chi-square distribution $\chi^2_p$ with $p$ degrees of freedom is the gamma law with shape $p/2$ and rate $1/2$ (scale $2$): the measure on $\mathbb{R}$ with density $x \mapsto \frac{(1/2)^{p/2}}{\Gamma(p/2)}\, x^{p/2 - 1} e^{-x/2}$ for $x > 0$ and $0$ for $x < 0$ with respect to Lebesgue measure. For $p \ge 1$ it is a probability measure on $[0, \infty)$. For $p = 0$ the definition is degenerate: $\Gamma(0)$ is taken to be $0$ and division by $0$ gives $0$, so the density vanishes and $\chi^2_0$ is the zero measure, not the point mass at $0$.

## Idea

For $p \ge 1$, the chi-square law is the law of $Z_1^2 + \dots + Z_p^2$ for independent standard normal $Z_i$, which is why it describes sample variances and goodness-of-fit statistics. The case $p = 1$ is a direct computation: $Z^2$ has law $\chi^2_1$. For general $p$ the moment generating function does the work. For $p \ge 1$ and $t < 1/2$, $\int e^{tx}\, d\chi^2_p(x) = (1 - 2t)^{-p/2}$, which for $p = 1$ is $\mathbb{E}[e^{tZ^2}] = 1/\sqrt{1 - 2t}$. Moment generating functions of chi-square laws multiply when the degrees of freedom add, just as the moment generating function of a sum of independent variables is the product of theirs.

## Statements

- [Chi-square distribution](chi-square-measure.md)
- [The square of a standard normal variable is chi-square with one degree of freedom](gaussian-real-map-sq.md): characterisation: square of a standard normal
- [Moment generating function of the chi-square distribution](mgf-chi-square-measure-of-lt.md): basic property: moment generating function
- [Chi-square moment generating functions multiply by adding degrees](prod-mgf-chi-square-measure-eq-mgf-sum.md): basic property: degrees of freedom add under independent sums
- [Exponential moments of the chi-square distribution](integrable-exp-mul-chi-square-measure.md): basic property: exponential moments
- [Moment generating function of the gamma law with shape and rate one half](mgf-gamma-measure-half-half-eq-sqrt.md): lemma used for the characterisation by squares of normal variables
- [Moment generating function of the square of a standard normal](mgf-sq-std-gaussian.md): lemma used for the characterisation by squares of normal variables
- [Moment generating function of the law of the square of a standard normal](mgf-id-map-sq-std-gaussian.md): lemma used for the characterisation by squares of normal variables
- [Exponential moments of the square of a standard normal](integrable-exp-mul-sq-std-gaussian.md): lemma used for the characterisation by squares of normal variables
- [Exponential moments of the law of the square of a standard normal](iio-subset-integrable-exp-set-map-sq-std.md): lemma used for the characterisation by squares of normal variables
- [Survival function of the chi-square distribution](chi-square-survival.md): definition: the upper tail
- [A chi-square law has no atoms](chi-square-measure-singleton.md): basic property: no atoms

## Background

- [Moment generating function of the gamma distribution](../gamma-distribution/gamma-mgf/README.md)
