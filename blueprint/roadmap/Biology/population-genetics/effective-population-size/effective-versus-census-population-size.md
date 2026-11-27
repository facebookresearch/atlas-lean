# Effective versus census population size in the fixation probability

In the diffusion approximation the fixation probability depends on the population only through the mean $M(p)$ and variance $V(p)$ of the change in gene frequency per generation: $u(p) = \int_0^pG(x)\,dx\big/\int_0^1G(x)\,dx$ with $G(x) = \exp\bigl(-\int_0^x 2M(y)/V(y)\,dy\bigr)$ (Kimura 1962, equations (3)–(4)). For genic selection with coefficient $s$ in a randomly mating population of $N$ diploids, $M(p) = sp(1 - p)$ and $V(p) = p(1 - p)/(2N)$ (equation (7)). The variance effective number $N_e$ is the value that gives variance $p(1 - p)/(2N_e)$ per generation (Kimura and Crow 1963). With this variance and $s \ne 0$, Kimura's formula gives $U(p) = (1 - e^{-4N_esp})/(1 - e^{-4N_es})$ (equation (8) with $N_e$ for $N$), and for $s = 0$ the neutral value $U(p) = p$. A new mutation is one copy among the $2N$ gene copies present, so its initial frequency $p = 1/(2N)$ is set by the census number, and for $s \ne 0$ (derivation)

$$U\Bigl(\frac{1}{2N}\Bigr) = \frac{1 - e^{-2sN_e/N}}{1 - e^{-4N_es}},$$

which is close to $2sN_e/N$ when $4N_es$ is large and $sN_e/N$ is small, and reduces to Kimura's $(1 - e^{-2s})/(1 - e^{-4Ns})$ (equation (10)) when $N_e = N$; for $s = 0$, $U(1/(2N)) = 1/(2N)$.

## Depends on

- [Effective population size and the variance in family size](../../../Biology/population-genetics/effective-population-size/effective-size-and-variance-in-family-size.md)
- [Kimura's fixation probability in terms of 4Ns, for nonzero Ns](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation-two-mul-mul.md)
- [Dirichlet ratio $S(p)/S(1)$ of the scale function](../diffusion-theory/selection-duality-and-general-one-dimensional-di/fixation-prob.md)
- [Inbreeding, variance and eigenvalue effective population sizes](effective-population-size-definitions.md)

## Expansion

1. The variance effective number from the conditional variance of the frequency change, and its agreement with the inbreeding effective number in the models of the family-size page (Kimura and Crow 1963).
2. The diffusion with $N_e$ in the infinitesimal variance and the resulting fixation probability $U(p)$.
3. The initial frequency $1/(2N)$ of a new mutation, the formula for $U(1/(2N))$ and its limits for large $4N_es$.
4. Models in which the variance and inbreeding effective numbers differ, so that no single effective size serves both, as separate statements with their own sources.

## Sources

- Original result: M. Kimura, On the probability of fixation of mutant genes in a population, Genetics 47 (1962), 713–719, equations (3)–(4) and (7)–(10). <https://doi.org/10.1093/genetics/47.6.713>
- M. Kimura and J. F. Crow, The measurement of effective population number, Evolution 17 (1963), 279–288. <https://doi.org/10.1111/j.1558-5646.1963.tb03281.x>
