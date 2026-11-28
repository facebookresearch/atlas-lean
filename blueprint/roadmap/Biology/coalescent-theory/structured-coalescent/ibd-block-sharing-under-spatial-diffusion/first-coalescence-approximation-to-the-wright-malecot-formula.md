# First-coalescence approximation to the Wright–Malécot formula

Let two genes be sampled at distance $r > 0$ in a two-dimensional population whose lineages follow the first-order [pairwise coalescence intensity](pairwise-coalescence-density-under-two-dimensional-diffusion.md) with constant effective density $D_e > 0$ and dispersal rate $\sigma > 0$. Assume each lineage mutates at rate $\mu > 0$ per generation and that two genes are identical by descent when no mutation occurs on either lineage before their common ancestor. Then, in the approximation in which the first coalescence is rare,

$$F(r) = \int_0^\infty \psi(t)\, e^{-2\mu t}\, dt = \frac{1}{4\pi D_e \sigma^2}\, K_0\!\left(\frac{\sqrt{2\mu}}{\sigma}\, r\right) = \frac{1}{\mathcal{N}} K_0\!\left(\frac{\sqrt{2\mu}}{\sigma}\, r\right),$$

where $\mathcal{N} = 4\pi D_e \sigma^2$ is Wright's neighbourhood size and $K_0$ is the modified Bessel function of the second kind of order zero. This is the leading term of the Wright–Malécot formula. It decays like $\sqrt{\pi \sigma/(2\sqrt{2\mu}\, r)}\, e^{-\sqrt{2\mu}\, r/\sigma}$ for $r \gg \sigma/\sqrt{2\mu}$ and diverges logarithmically as $r \to 0$, which is where a local-scale correction to the denominator is needed. Replacing $\mu$ by the block length $L$ in $e^{-2\mu t}$ gives the probability that no crossover falls on a segment of length $L$, but not the density of blocks: the [IBD block-sharing formula](expected-ibd-block-sharing-under-spatial-diffusion.md) also multiplies $e^{-2Lt}$ by the endpoint factors $(2t)^2$ (two flanking crossovers) and $2 \cdot 2t$ (one flanking crossover and a chromosome end), and these powers of $t$ raise the Bessel order from $0$ to $2$ and $1$ at constant density.

## Proof sketch

With constant $D_e$ the integrand is $\frac{1}{8\pi D_e \sigma^2}\, t^{-1} \exp(-a/t - bt)$ with $a = r^2/(4\sigma^2)$ and $b = 2\mu$. The representation $\int_0^\infty t^{\nu-1} e^{-a/t - bt}\, dt = 2(a/b)^{\nu/2} K_\nu(2\sqrt{ab})$ at $\nu = 0$ gives $2 K_0(\sqrt{2\mu}\, r/\sigma)$. The divergence at $r = 0$ reflects that the diffusion approximation is not valid at scales below the local dispersal scale; a careful treatment adds to $\mathcal{N}$ in the denominator a logarithmic term involving a local scale that depends on the fine-scale details of the model.

## Depends on

- [Pairwise coalescence density under two-dimensional diffusion of ancestry](pairwise-coalescence-density-under-two-dimensional-diffusion.md)

## Sources

- H. Ringbauer, G. Coop and N. H. Barton, Inferring recent demography from isolation by distance of long shared sequence blocks, *Genetics* 205 (2017), 1335–1351, <https://doi.org/10.1534/genetics.116.196220>, PMCID PMC5340342 (Discussion: comparison with the Wright–Malécot formula, $\lambda = \mu$ versus $\lambda = L$).
- N. H. Barton, F. Depaulis and A. M. Etheridge, Neutral evolution in spatially continuous populations, *Theor. Popul. Biol.* 61 (2002), 31–48, <https://doi.org/10.1006/tpbi.2001.1557>.
