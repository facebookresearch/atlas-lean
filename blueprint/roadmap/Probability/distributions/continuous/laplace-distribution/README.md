# Laplace distribution

For real $m$ and $b$, the Laplace law $\mathrm{Lap}(m, b)$ is the measure on $\mathbb{R}$ with density $z \mapsto \max\bigl(e^{-|z - m|/b} / (2b), 0\bigr)$ with respect to Lebesgue measure. For $b > 0$ the density is $e^{-|z - m|/b}/(2b)$ and $\mathrm{Lap}(m, b)$ is a probability law with location $m$ and scale $b$. For $b \le 0$ it is the zero measure: for $b < 0$ the formula is negative, and for $b = 0$ it reads $e^0/0 = 0$, with division by zero read as $0$.

## Idea

For $b > 0$ the Laplace law is a symmetric, two-sided exponential law around $m$. It has a sharp peak at $m$ and tails heavier than a normal law's. It is the noise of the Laplace mechanism of differential privacy and the prior behind the lasso. Its key property for privacy is a stability bound under shifts. Moving the location from $m'$ to $m$ multiplies the density at any point by at most $e^{|m - m'|/b}$, so $\mathrm{Lap}(m, b) \le e^{|m - m'|/b}\, \mathrm{Lap}(m', b)$ as measures. Adding $\mathrm{Lap}(0, \Delta/\varepsilon)$ noise to a query whose value moves by at most $\Delta$ therefore changes the probability of any event by a factor at most $e^{\varepsilon}$.

## Statements

- [Laplace distribution](laplace-measure.md)
- [Density of the Laplace distribution](laplace-pdfreal.md): definition used in the main definition
- [The Laplace density integrates to one](integral-laplace-pdfreal.md): lemma: normalisation of the density
- [The Laplace law is a probability measure](is-probability-measure-laplace-measure.md): basic property: a probability measure
- [Shifting the Laplace density](laplace-pdfreal-le-exp-mul.md): lemma: shift bound for the density
- [Laplace laws at nearby locations](laplace-measure-le-smul.md): basic property: laws at nearby locations are comparable

## Background

- [Exponential distribution](../exponential-distribution/README.md): the Laplace law is the law of $m + \sigma E$ with $E$ exponential of rate $1/b$ and $\sigma = \pm 1$ an independent fair sign, its symmetric version.

## Related topics

- [Laplace and exponential mechanisms](../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/README.md): the Laplace mechanism of differential privacy adds Laplace noise calibrated to the sensitivity of a query.
