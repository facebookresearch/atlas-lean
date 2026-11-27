# Segregating sites in the Poisson random field form a Poisson point process

In the Poisson random field model of Sawyer and Hartl (1992), new mutations arise at Poisson times, each at a new site (infinite sites, irreversible), and the frequency of each mutant follows an independent Wright–Fisher path. Under these assumptions the population frequencies of the segregating sites at stationarity form a Poisson point process on $(0, 1)$ with intensity $\varphi_{\theta,\sigma}(x)\,dx$, the [Sawyer–Hartl density](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/prf-density.md), whose neutral case $\theta/x$ is obtained from the Green's function (Sawyer and Hartl 1992). The target is this distributional statement about the population configuration; its consequence for samples, that binomial sampling turns the process into independent Poisson counts per frequency class, is stated with the likelihood in [Expected joint allele-frequency spectrum and its Poisson likelihood](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md).

## Depends on

- [Sawyer–Hartl Poisson random field density](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/prf-density.md)
- [The neutral density from the Green's function](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/prf-density-zero-eq-neutral-green.md)

## Expansion

1. The influx model: a Poisson process of mutation origins in time with independent diffusion paths, each started at frequency $1/(2N)$.
2. The occupation density: for the neutral diffusion, $G(p, x) = 2p/x$ for $x > p$ and $2(1 - p)/(1 - x)$ for $x < p$, and its limit at $p = 1/(2N)$.
3. The stationary Poisson random field with intensity $\theta/x$, $\theta = 4N\mu$, and its infinite total mass.

## Sources

- Original result: S. A. Sawyer and D. L. Hartl, Population genetics of polymorphism and divergence, Genetics 132 (1992), 1161–1176. <https://doi.org/10.1093/genetics/132.4.1161>
