# Effective versus census population size in the fixation probability

In the diffusion approximation the population size enters only through the variance of the change in gene frequency per generation, $V(p) \approx p(1 - p)/(2N)$ for a Wright–Fisher population of $N$ diploids (Felsenstein, Section VII.8, equations (VII-87)–(VII-88)). The variance effective number $N_e$ is the value that gives variance $p(1 - p)/(2N_e)$ per generation; Felsenstein notes that it usually coincides with the inbreeding effective number in the cases treated, substitutes $N_e$ for $N$, and obtains the criterion $4N_es > 1$ for selection to be effective against drift. With multiplicative selection the fixation probability is then $U(p) = (1 - e^{-4N_esp})/(1 - e^{-4N_es})$ (equation (VII-91) with $N_e$ for $N$). A new mutation is one copy among the $2N$ gene copies present, so its initial frequency $p = 1/(2N)$ is set by the census number, and (derivation)

$$U\Bigl(\frac{1}{2N}\Bigr) = \frac{1 - e^{-2sN_e/N}}{1 - e^{-4N_es}},$$

which is close to $2sN_e/N$ when $4N_es$ is large and $sN_e/N$ is small, and reduces to Felsenstein's $(1 - e^{-2s})/(1 - e^{-4Ns})$ (equation (VII-93)) when $N_e = N$.

## Depends on

- [Effective population size and the variance in family size](../../../Biology/population-genetics/effective-population-size/effective-size-and-variance-in-family-size.md)
- [Kimura's fixation probability in terms of 4Ns, for nonzero Ns](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation-two-mul-mul.md)

## Expansion

1. The variance effective number from the conditional variance of the frequency change, and its agreement with the inbreeding effective number in the models of the family-size page.
2. The diffusion with $N_e$ in the infinitesimal variance and the resulting fixation probability $U(p)$.
3. The initial frequency $1/(2N)$ of a new mutation, the formula for $U(1/(2N))$ and its limits for large $4N_es$.
4. Models in which the variance and inbreeding effective numbers differ, so that no single effective size serves both, as separate statements with their own sources.

## Sources

- J. Felsenstein, Theoretical Evolutionary Genetics, course text, University of Washington, Section VII.8, equations (VII-87)–(VII-93) and the subsection Departures from the Wright–Fisher model: effective population number.
- Original result: M. Kimura, On the probability of fixation of mutant genes in a population, Genetics 47 (1962), 713–719. <https://doi.org/10.1093/genetics/47.6.713> The fixation probability formula follows Felsenstein, Section VII.8.
