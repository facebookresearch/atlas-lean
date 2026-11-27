# Invariance of fixation probabilities under conservative migration

In the structured diffusion with generator $Lf = \sum_i\frac{x_i(1 - x_i)}{2\kappa_i}\partial_i^2f + \sum_i\bigl[\sum_{j \ne i}q_{ij}(x_j - x_i) + \alpha x_i(1 - x_i)\bigr]\partial_if$, assume that migration is conservative, that is, the census weights $w_i = \kappa_i/K$, $K = \sum_k\kappa_k$, satisfy $w^TQ = 0$, equivalently $\sum_{i \ne j}\kappa_iq_{ij} = \kappa_j\sum_{k \ne j}q_{jk}$ for every deme $j$, that selection is genic with the same scaled coefficient $\alpha$ in every deme, and that the migration graph is connected. Then the probability that the allele fixes is the panmictic formula for a population of $K$ times the reference size,

$$u(\bar x) = \begin{cases}\dfrac{1 - e^{-2\alpha K\bar x}}{1 - e^{-2\alpha K}}, & \alpha \ne 0,\\[1ex] \bar x, & \alpha = 0,\end{cases} \qquad \bar x = \sum_iw_ix_i,$$

whatever the migration rates.

Proof. Let $H(x) = \sum_iw_ix_i(1 - x_i)$. Migration does not change $\bar x$, so the drift of $\bar x$ is $\alpha H(x)$; since the demes resample independently, its quadratic-variation rate is $\sum_iw_i^2x_i(1 - x_i)/\kappa_i = H(x)/K$, because $w_i/\kappa_i = 1/K$. For $f(x) = e^{-2\alpha K\bar x}$,

$$Lf = f\Bigl(-2\alpha K\cdot\alpha H + \tfrac12(2\alpha K)^2\frac{H}{K}\Bigr) = 0,$$

so for $\alpha \ne 0$, $e^{-2\alpha K\bar x(t)}$ is a bounded martingale, and optional stopping at the absorption time gives $u$. For $\alpha = 0$ the drift of $\bar x$ vanishes, so $\bar x(t)$ is itself a bounded martingale and optional stopping gives $u(\bar x) = \bar x$. The argument uses that the drift of $\bar x$ is a constant multiple of its quadratic-variation rate; this compatibility holds under the three assumptions above. Cherry and Wakeley (2003, abstract) find for Wright's island model with genic selection that the fixation probability is unaffected by subdivision, because the equivalent panmictic population has a larger effective size and a smaller effective selection coefficient with unchanged product; Whitlock (2003, abstract) notes that earlier results of this kind assume that every deme contributes to the next generation in exact proportion to its size and that alleles are additive.

## Depends on

- [Neutral fixation probability in a structured population](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/neutral-fixation-with-reproductive-weights.md)
- [Closed form of Kimura's fixation probability for nonzero σ](../../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/kimura-fixation-eq-of-ne-zero.md)

## Proof depends on

- [Multidimensional Itô formula and covariation](../../../../Probability/stochastic-calculus/it-s-formula/multidimensional-ito-formula-and-covariation.md)

## Expansion

1. The structured diffusion with genic selection, conservative migration and local resampling.
2. The drift $\alpha H$ and the quadratic-variation rate $H/K$ of $\bar x$ under census weights.
3. The martingale $e^{-2\alpha K\bar x(t)}$ and the fixation probability by optional stopping.
4. The neutral case $\alpha = 0$, where $\bar x(t)$ is a martingale and $u(\bar x) = \bar x$, which is also the limit of the selected formula as $\alpha \to 0$.

## Sources

- J. L. Cherry and J. Wakeley, A diffusion approximation for selection and drift in a subdivided population, Genetics 163 (2003), 421–428, abstract. <https://doi.org/10.1093/genetics/163.1.421>
- M. C. Whitlock, Fixation probability and time in subdivided populations, Genetics 164 (2003), 767–779, abstract. <https://doi.org/10.1093/genetics/164.2.767>
