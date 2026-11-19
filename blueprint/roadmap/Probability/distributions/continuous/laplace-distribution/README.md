# Laplace distribution

The Laplace distribution with location $m$ and scale $b > 0$ has density $\exp(-|z - m|/b)/(2b)$: a symmetric, two-sided exponential law. It is the noise of the Laplace mechanism of differential privacy and the prior behind the lasso.

- [Density of the Laplace distribution](laplace-pdfreal.md)
- [Laplace distribution](laplace-measure.md)
- [The Laplace density integrates to one](integral-laplace-pdfreal.md)
- [The Laplace law is a probability measure](is-probability-measure-laplace-measure.md)
- [Shifting the Laplace density](laplace-pdfreal-le-exp-mul.md)
- [Laplace laws at nearby locations](laplace-measure-le-smul.md)

## Related topics

- [Exponential distribution](../exponential-distribution/README.md): the Laplace law is the law of $m + \sigma E$ with $E$ exponential of rate $1/b$ and $\sigma = \pm 1$ an independent fair sign, its symmetric version.
- [Laplace and exponential mechanisms](../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/README.md): the Laplace mechanism of differential privacy adds Laplace noise calibrated to the sensitivity of a query.
