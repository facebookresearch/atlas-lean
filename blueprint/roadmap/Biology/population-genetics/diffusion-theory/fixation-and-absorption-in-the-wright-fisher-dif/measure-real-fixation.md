# Kimura's fixation probability, process form

Let $\sigma$ and $x$ be real, $\mu$ a probability measure and $(X_t)_{t \ge 0}$ a [solution of the Wright–Fisher martingale problem](is-wright-fisher-solution.md) with selection coefficient $\sigma$ under $\mu$, with $X_0 = x$ almost surely. Then the probability that the allele is eventually fixed, $\mu(\exists t_0,\ \forall t \ge t_0,\ X_t = 1)$, equals [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md)

$$u_\sigma(x) = \frac{1 - e^{-2\sigma x}}{1 - e^{-2\sigma}} \quad (\sigma \ne 0), \qquad u_0(x) = x.$$

## Sources

- M. Kimura, *On the probability of fixation of mutant genes in a population*, Genetics 47 (1962), 713–719.
- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
