# Expected IBD block sharing under two-dimensional diffusion of ancestry

Let two haploid genomes be sampled at geographic distance $r > 0$, and let their ancestry follow the [pairwise coalescence density](pairwise-coalescence-density-under-two-dimensional-diffusion.md) $\psi(t)$ with dispersal rate $\sigma > 0$. Recombination along a chromosome of map length $G$ (in Morgans) occurs as a Poisson process of rate $1$ per Morgan per meiosis, and an IBD block is a maximal segment not interrupted by recombination on either lineage before the common ancestor. For $t$ generations back there are $2t$ meioses, so the expected density (per unit block length) of blocks of length $L$ produced by coalescence at time $t$ is

$$\mathbb{E}[K_{L,t}] = 2 \cdot 2t\, e^{-2Lt} + (G - L)\, (2t)^2 e^{-2Lt} \approx G\, 4t^2 e^{-2Lt} \qquad (L \ll G),$$

the first term counting blocks touching a chromosome end. Suppose the effective density follows the power law $D_e(t) = D t^{-\beta}$ with $D > 0$ and $\beta \in \mathbb{R}$ ($\beta = 0$ constant, $\beta > 0$ growth towards the present, $\beta < 0$ decline). Then the expected density of shared blocks of length $L > 0$ is

$$\mathbb{E}[N_L] = \int_0^\infty \mathbb{E}[K_{L,t}]\, \psi(t)\, dt = 2^{-\frac{3\beta}{2} - 3} \frac{G}{\pi D \sigma^2} \left(\frac{r}{\sqrt{L}\,\sigma}\right)^{2+\beta} K_{2+\beta}\!\left(\sqrt{2L}\, \frac{r}{\sigma}\right),$$

where $K_\nu$ is the modified Bessel function of the second kind of order $\nu$, and the expected number of blocks longer than $L_0 > 0$ is

$$\mathbb{E}[N_{>L_0}] = \int_{L_0}^\infty \mathbb{E}[N_L]\, dL = 2^{-\frac{5 + 3\beta}{2}} \frac{G}{\pi D \sigma^2} \left(\frac{r}{\sqrt{L_0}\,\sigma}\right)^{1+\beta} K_{1+\beta}\!\left(\sqrt{2 L_0}\, \frac{r}{\sigma}\right).$$

For constant density ($\beta = 0$) this is $\mathbb{E}[N_L] = \dfrac{G}{8\pi D \sigma^2} \left(\dfrac{r}{\sqrt{L}\,\sigma}\right)^{2} K_{2}\!\left(\sqrt{2L}\, r/\sigma\right)$.

## Depends on

- [Pairwise coalescence density under two-dimensional diffusion of ancestry](pairwise-coalescence-density-under-two-dimensional-diffusion.md)

## Expansion

With $L \ll G$ the integrand is $\frac{G t^{1+\beta}}{2\pi D \sigma^2} \exp\!\left(-\frac{a}{t} - b t\right)$ with $a = r^2/(4\sigma^2)$ and $b = 2L$. The integral representation $\int_0^\infty t^{\nu - 1} e^{-a/t - bt}\, dt = 2 (a/b)^{\nu/2} K_\nu(2\sqrt{ab})$ for $a, b > 0$, applied with $\nu = 2 + \beta$, gives $(a/b)^{\nu/2} = 2^{-3\nu/2} (r/(\sqrt{L}\sigma))^{\nu}$ and $2\sqrt{ab} = \sqrt{2L}\, r/\sigma$, which is the formula for $\mathbb{E}[N_L]$. The integral converges for every real $\beta$ because $r > 0$ makes $e^{-a/t}$ kill the small-$t$ region; for exponential growth $D_e(t) \propto e^{-\beta t}$ it converges only when $2L > \beta$. Integrating in $L$ uses $\frac{d}{dx}\left(x^{-\nu} K_\nu(x)\right) = -x^{-\nu} K_{\nu+1}(x)$. Including the chromosome-end term $4t e^{-2Lt}$ adds a second Bessel term of the same form with $\beta$ replaced by $\beta - 1$. A composite likelihood treating block counts in small length bins as independent Poisson variables with these means fits $\sigma$, $D$ and $\beta$.

## Sources

- H. Ringbauer, G. Coop and N. H. Barton, Inferring recent demography from isolation by distance of long shared sequence blocks, *Genetics* 205 (2017), 1335–1351, <https://doi.org/10.1534/genetics.116.196220>, PMCID PMC5340342 (Equations 2–5 and 7–11; Appendices B and C).
- N. H. Barton, A. M. Etheridge, J. Kelleher and A. Véber, Inference in two dimensions: allele frequencies versus lengths of shared sequence blocks, *Theor. Popul. Biol.* 87 (2013), 105–119, <https://doi.org/10.1016/j.tpb.2013.03.001>.
