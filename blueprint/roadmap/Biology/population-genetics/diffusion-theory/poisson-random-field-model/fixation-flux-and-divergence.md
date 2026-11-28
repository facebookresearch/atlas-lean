# Fixation flux and divergence in the Poisson random field

In the Poisson random field model with scaled mutation rate $\theta = 4N\mu$, for the per-generation mutation rate $\mu$, and scaled selection coefficient $\sigma$, the probability current of the Sawyer–Hartl density through $(0, 1)$ is $\theta\sigma/(1 - e^{-2\sigma})$, and $\theta/2$ in the neutral case ([probability current](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/current-prf-density.md)). The expected number of fixed differences accumulated in a lineage over a time $t_{\mathrm{div}}$ (in units of $2N$ generations) is the number of new mutations times the fixation probability of each: in the neutral case $\frac\theta2\,t_{\mathrm{div}}\cdot 2N\cdot\frac1{2N} = \frac\theta2t_{\mathrm{div}}$ in these units, that is $\mu$ per generation, and with selection the fixation probability $u_\sigma(\frac1{2N})$ replaces $\frac1{2N}$ (Sawyer and Hartl 1992). That the number of sites fixed by a given time is asymptotically Poisson, with an explicit mean, is stated in the Moran scaling on [Time-inhomogeneous Poisson random field with legacy polymorphisms](time-dependent-poisson-random-fields/time-inhomogeneous-poisson-random-field-with-legacy-polymorphisms.md) (its theorem on fixations) and is not restated here. The target is the identification of the expected substitution rate with the probability current at the upper boundary, and the number of substitutions as a Poisson counting process in time, beyond the Poisson law of the count at a single time.

## Depends on

- [Probability current of the Poisson random field density](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/current-prf-density.md)
- [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md)

## Proof depends on

- [Exponential interarrivals give a Poisson process](../../../../Probability/point-processes/poisson-processes/is-poisson-process-count.md)
- [Time-inhomogeneous Poisson random field with legacy polymorphisms](time-dependent-poisson-random-fields/time-inhomogeneous-poisson-random-field-with-legacy-polymorphisms.md)

## Expansion

1. The Poisson random field density with selection and its [probability current](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/current-prf-density.md).
2. The current at the upper boundary as the rate of fixations, from the forward equation and the influx boundary condition.
3. The limit $2N\,u_\sigma(\frac1{2N}) \to u_\sigma'(0) = 2\sigma/(1 - e^{-2\sigma})$, and the per-generation rate $\mu\cdot 2\sigma/(1 - e^{-2\sigma})$.
4. The neutral check: substitution rate $\mu$ per generation, from the [neutral fixation probability](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation-neutral.md).

## Sources

- Original result: S. A. Sawyer and D. L. Hartl, Population genetics of polymorphism and divergence, Genetics 132 (1992), 1161–1176. <https://doi.org/10.1093/genetics/132.4.1161>
