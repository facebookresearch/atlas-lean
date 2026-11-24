# Site-frequency counts in the Poisson random field are independent Poisson

In the Poisson random field model of Sawyer and Hartl (1992), new mutations arise at Poisson times, each at a new site (infinite sites, irreversible), and the frequency of each mutant follows an independent Wright–Fisher path. The expected spectrum of a sample of $n$ gene copies is $E\xi_i = \int_0^1\binom ni x^i(1 - x)^{n-i}\varphi_{\theta,\sigma}(x)\,dx$ with the Sawyer–Hartl density $\varphi_{\theta,\sigma}$, whose neutral case $\theta/x$ is obtained from the Green's function. Under these assumptions the counts $\xi_1, \dots, \xi_{n-1}$ themselves are independent Poisson random variables with these means (Sethupathy and Hannenhalli 2008, Sec. 4, after Sawyer and Hartl 1992); in the neutral case $\xi_i \sim \mathrm{Poisson}(\theta/i)$, independently. The target is this distributional statement: the segregating sites at stationarity form a Poisson point process in frequency space with intensity $\varphi_{\theta,\sigma}$, and the sample counts are independent Poisson by the marking theorem.

## Depends on

- [Expected site frequency spectrum under the Poisson random field](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/expected-sfs.md)
- [The neutral density from the Green's function](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/prf-density-zero-eq-neutral-green.md)

## Expansion

1. The influx model: a Poisson process of mutation origins in time with independent diffusion paths, each started at frequency $1/(2N)$.
2. The occupation density: for the neutral diffusion, $G(p, x) = 2p/x$ for $x > p$ and $2(1 - p)/(1 - x)$ for $x < p$, and its limit at $p = 1/(2N)$.
3. The stationary Poisson random field with intensity $\theta/x$, $\theta = 4N\mu$, and its infinite total mass.
4. Sample counts as independent Poisson variables by the marking theorem, and the [expected site frequency spectrum under the Poisson random field](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/expected-sfs.md) and [neutral spectrum](../../../../Biology/population-genetics/diffusion-theory/poisson-random-field-model/expected-sfs-neutral.md).

## Sources

- Original result: S. A. Sawyer and D. L. Hartl, Population genetics of polymorphism and divergence, Genetics 132 (1992), 1161–1176. <https://doi.org/10.1093/genetics/132.4.1161> The spectrum follows Sethupathy and Hannenhalli (2008).
- P. Sethupathy and S. Hannenhalli, A tutorial of the Poisson random field model in population genetics, Adv. Bioinformatics 2008 (2008), 257864. <https://doi.org/10.1155/2008/257864>
