# Flat-prior posterior of the observed/expected ratio

Let $E$ be a real number, $\gamma \ge 0$ a real number and $o$ a natural number. Then

$$E \cdot L(\gamma E, o) = \frac{E^{o+1}}{\Gamma(o+1)}\, \gamma^{o} e^{-E\gamma},$$

where $L$ is the [Poisson likelihood](poisson-lik.md); the right side is the density at $\gamma$ of the Gamma distribution with shape $o + 1$ and rate $E$.

For $E > 0$ that density integrates to one, so the likelihood $\gamma \mapsto L(\gamma E, o)$ of $o$ observed loss-of-function variants with $E$ expected, normalized as a flat-prior posterior, is the Gamma distribution of shape $o+1$ and rate $E$; the identity itself holds for every real $E$.
