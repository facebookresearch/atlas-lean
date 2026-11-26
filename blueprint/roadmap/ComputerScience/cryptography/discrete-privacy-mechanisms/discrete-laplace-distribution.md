# The discrete Laplace (two-sided geometric) distribution

For $\alpha \in [0, 1)$, the *two-sided geometric distribution* gives each integer $z$ the mass

$$
\frac{1 - \alpha}{1 + \alpha}\,\alpha^{|z|}.
$$

With $\alpha = e^{-1/s}$ it is the *discrete Laplace distribution* of scale $s$. The *geometric mechanism* releases $f(x) + Z$ for an integer-valued query $f$ and $Z$ discrete Laplace.

## Depends on

- [Laplace distribution](../../../Probability/distributions/continuous/laplace-distribution/laplace-measure.md)

## Sources

- Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan, "Universally Utility-Maximizing Privacy Mechanisms", SIAM Journal on Computing, 2012.
- Clément L. Canonne, Gautam Kamath and Thomas Steinke, "The Discrete Gaussian for Differential Privacy", Advances in Neural Information Processing Systems 33, 2020.
