# Invariance of integrated heterozygosity under geographical structure

In the neutral structured diffusion with conservative migration, a connected migration graph (the rate matrix $Q = (q_{ij})$ irreducible, so that the process is absorbed at a monomorphic state almost surely) and census weights $w_i = \kappa_i/K$, let $H(x) = \sum_iw_ix_i(1 - x_i)$ be the census-weighted local heterozygosity (one half of the mean probability that two genes drawn from the same deme differ), $\bar x = \sum_iw_ix_i$ the total frequency, and $\tau$ the absorption time. For every continuous $g$ on $[0, 1]$,

$$E_x\int_0^\tau g(\bar x(t))\,H(x(t))\,dt = 2K\int_0^1\min(p, y)\bigl(1 - \max(p, y)\bigr)g(y)\,dy, \qquad p = \bar x(0).$$

The right side depends only on $p$, $K$ and $g$, so the expected heterozygosity accumulated while the total frequency lies in any set is the same for every conservative migration pattern and every way of dividing the population into demes, and equals its value for a panmictic population of the same total size. The local heterozygosity itself and its time course do depend on the structure. A genealogical invariance under conservative migration is the [size-weighted within-deme coalescence-time invariance](../../../coalescent-theory/structured-coalescent/strobeck-nagylaki-invariance-size-weighted-mean.md).

Proof. The total frequency is a martingale with quadratic-variation rate $H/K$. Let $f(y) = 2\int_0^1\min(y, z)(1 - \max(y, z))g(z)\,dz$, so that $f'' = -2g$ and $f(0) = f(1) = 0$. By Itô's formula $f(\bar x(t)) + \frac1K\int_0^tg(\bar x(s))H(x(s))\,ds$ is a martingale; the absorption time has finite mean and $f$ and $g$ are bounded, so optional stopping at $\tau$, where $\bar x(\tau) \in \{0, 1\}$, gives the identity. Maruyama (Genetics 1974; Theor. Popul. Biol. 1974) showed for the neutral model of colonies connected by migration that a stochastic clock equal to the summed average local genetic variation turns the total frequency into a process independent of the geographical structure, and that the fixation probability of a mutant and the local genetic variation summed over the generations in which the total frequency takes a specified value are independent of that structure; the identity above is the diffusion form of the latter.

## Depends on

- [A random clock for the total allele frequency in a structured population](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/maruyama-stochastic-clock.md)
- [Dynkin's formula and optional stopping for diffusions on the unit interval](../../../../Probability/stochastic-calculus/one-dimensional-diffusions/dynkin-formula-and-stopping.md)

## Proof depends on

- [Itô's formula for continuous semimartingales with bounded derivatives](../../../../Probability/stochastic-calculus/it-s-formula/ito-formula-for-continuous-semimartingales-bound.md)

## Expansion

1. The heterozygosity functional and the quadratic variation $H/K$ of the total frequency.
2. The Green-function solution $f$ of $f'' = -2g$ with zero boundary values.
3. Itô's formula, finiteness of the mean absorption time, and optional stopping.
4. The new-mutation case $p = 1/(KM)$ and the version conditioned on fixation, obtained by weighting $g$ with $y/p$.

## Sources

- Original result: T. Maruyama, A Markov process of gene frequency change in a geographically structured population, Genetics 76 (1974), 367–377. <https://doi.org/10.1093/genetics/76.2.367>
- Original result: T. Maruyama, A simple proof that certain quantities are independent of the geographical structure of population, Theor. Popul. Biol. 5 (1974), 148–154. <https://doi.org/10.1016/0040-5809(74)90037-9>
