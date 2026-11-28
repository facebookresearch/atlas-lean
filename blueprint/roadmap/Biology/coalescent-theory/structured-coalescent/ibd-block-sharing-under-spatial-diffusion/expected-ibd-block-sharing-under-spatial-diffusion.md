# Expected IBD block sharing under two-dimensional diffusion of ancestry

Let two haploid genomes be sampled at geographic distance $r > 0$, and let their ancestry follow the first-order [pairwise coalescence intensity](pairwise-coalescence-density-under-two-dimensional-diffusion.md) $\psi(t)$ with dispersal rate $\sigma > 0$. Recombination along a chromosome of map length $G$ (in Morgans) occurs as a Poisson process of rate $1$ per Morgan per meiosis, and an IBD block is a maximal segment not interrupted by recombination on either lineage before the common ancestor. For $t$ generations back there are $2t$ meioses, so for $0 < L < G$ the expected density (per unit block length) of blocks of length $L$ produced by coalescence at time $t$ is

$$\mathbb{E}[K_{L,t}] = 2 \cdot 2t\, e^{-2Lt} + (G - L)\, (2t)^2 e^{-2Lt},$$

the first term counting blocks touching exactly one chromosome end. In addition, with probability $e^{-2Gt}$ no crossover falls on the chromosome in the $2t$ meioses, and the whole chromosome is one block of length exactly $G$; this atom at $L = G$ is not part of the density. No block is longer than $G$, so $\mathbb{E}[K_{L,t}] = 0$ for $L > G$. Suppose the effective density follows the power law $D_e(t) = D t^{-\beta}$ with $D > 0$ and $\beta \in \mathbb{R}$ ($\beta = 0$ constant, $\beta > 0$ growth towards the present, $\beta < 0$ decline). Write

$$n_L(\beta) = \frac{2^{-\frac{3\beta}{2} - 3}}{\pi D \sigma^2} \left(\frac{r}{\sqrt{L}\,\sigma}\right)^{2+\beta} K_{2+\beta}\!\left(\sqrt{2L}\, \frac{r}{\sigma}\right),$$

where $K_\nu$ is the modified Bessel function of the second kind of order $\nu$. Then the expected density of shared blocks of length $L$ on the chromosome is

$$\mathbb{E}[N_L] = \int_0^\infty \mathbb{E}[K_{L,t}]\, \psi(t)\, dt = (G - L)\, n_L(\beta) + n_L(\beta - 1) \qquad (0 < L < G),$$

and $\mathbb{E}[N_L] = 0$ for $L > G$. The expected number of whole-chromosome blocks is

$$\int_0^\infty e^{-2Gt}\, \psi(t)\, dt = \tfrac14\, n_G(\beta - 2),$$

so the expected number of blocks longer than $L_0$ is

$$\mathbb{E}[N_{>L_0}] = \int_{L_0}^{G} \mathbb{E}[N_L]\, dL + \tfrac14\, n_G(\beta - 2) \qquad (0 < L_0 < G),$$

and $\mathbb{E}[N_{>L_0}] = 0$ for $L_0 \ge G$. Restricting to blocks strictly shorter than $G$ drops the second term.

The density $(G - L)\,n_L(\beta) + n_L(\beta - 1)$ is the source's finite-chromosome result (its Equation 4 integrated against $\psi$, Appendix B). The whole-chromosome atom, its expected count $\tfrac14\, n_G(\beta - 2)$, and the exact finite-chromosome tail $\mathbb{E}[N_{>L_0}]$ are derived on this page and are not printed in the source, which gives only the edge-free tail below (its Equation 10).

**Edge-free approximation.** For $L \ll G$ the chromosome-end term and the $-L$ in $G - L$ are negligible, and one uses $\mathbb{E}[N_L] \approx G\, n_L(\beta)$, extended to all $L > 0$. Under this approximation the tail is

$$\mathbb{E}[N_{>L_0}] \approx G \int_{L_0}^\infty n_L(\beta)\, dL = 2^{-\frac{5 + 3\beta}{2}} \frac{G}{\pi D \sigma^2} \left(\frac{r}{\sqrt{L_0}\,\sigma}\right)^{1+\beta} K_{1+\beta}\!\left(\sqrt{2 L_0}\, \frac{r}{\sigma}\right),$$

which is not the exact tail; in particular it is positive for $L_0 \ge G$. For constant density ($\beta = 0$) the edge-free density is $G\, n_L(0) = \dfrac{G}{8\pi D \sigma^2} \left(\dfrac{r}{\sqrt{L}\,\sigma}\right)^{2} K_{2}\!\left(\sqrt{2L}\, r/\sigma\right)$.

## Proof sketch

The pairwise coalescence intensity is $\psi(t) = \frac{t^{\beta - 1}}{8\pi D \sigma^2} e^{-a/t}$ with $a = r^2/(4\sigma^2)$, so the bulk term $(G - L)(2t)^2 e^{-2Lt}\psi(t)$ is $\frac{(G - L)\, t^{1+\beta}}{2\pi D \sigma^2} \exp\!\left(-\frac{a}{t} - b t\right)$ with $b = 2L$. The integral representation $\int_0^\infty t^{\nu - 1} e^{-a/t - bt}\, dt = 2 (a/b)^{\nu/2} K_\nu(2\sqrt{ab})$ for $a, b > 0$, applied with $\nu = 2 + \beta$, gives $(a/b)^{\nu/2} = 2^{-3\nu/2} (r/(\sqrt{L}\sigma))^{\nu}$ and $2\sqrt{ab} = \sqrt{2L}\, r/\sigma$, hence $(G - L)\, n_L(\beta)$. The chromosome-end term $4t e^{-2Lt}\psi(t)$ has one power of $t$ fewer and no factor $G - L$, which is the same computation with $\beta$ replaced by $\beta - 1$, hence $n_L(\beta - 1)$. The whole-chromosome term (derived on this page) $e^{-2Gt}\psi(t)$ has two powers of $t$ fewer than the bulk term and $b = 2G$: the representation with $\nu = \beta$ gives $\frac{1}{4\pi D\sigma^2} 2^{-3\beta/2} (r/(\sqrt{G}\sigma))^{\beta} K_\beta(\sqrt{2G}\, r/\sigma) = \tfrac14 n_G(\beta - 2)$. The integrals converge for every real $\beta$ because $r > 0$ makes $e^{-a/t}$ kill the small-$t$ region; for exponential growth $D_e(t) \propto e^{-\beta t}$ they converge only when $2L > \beta$. Integrating the edge-free density in $L$ uses $\frac{d}{dx}\left(x^{-\nu} K_\nu(x)\right) = -x^{-\nu} K_{\nu+1}(x)$. A composite likelihood treating block counts in small length bins as independent Poisson variables with these means fits $\sigma$, $D$ and $\beta$.

## Depends on

- [Pairwise coalescence density under two-dimensional diffusion of ancestry](pairwise-coalescence-density-under-two-dimensional-diffusion.md)

## Sources

- H. Ringbauer, G. Coop and N. H. Barton, Inferring recent demography from isolation by distance of long shared sequence blocks, *Genetics* 205 (2017), 1335–1351, <https://doi.org/10.1534/genetics.116.196220>, PMCID PMC5340342 (Equations 2–5 and 7–11, with Equation 4 the finite-chromosome density and Equation 5 its edge-free approximation; Appendices B and C). The whole-chromosome block count and the exact finite-chromosome tail are derived on this page; the source does not state them.
- N. H. Barton, A. M. Etheridge, J. Kelleher and A. Véber, Inference in two dimensions: allele frequencies versus lengths of shared sequence blocks, *Theor. Popul. Biol.* 87 (2013), 105–119, <https://doi.org/10.1016/j.tpb.2013.03.001>.
