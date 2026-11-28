# Two-locus frequency spectrum and its composite likelihood

**Population model.** Two biallelic loci $A/a$ and $B/b$ (derived alleles $A$, $B$) with population-scaled recombination rate $\rho = 4N_A r$ evolve in a randomly mating population of relative size $\nu(\tau) = N(\tau)/N_A$, with time $\tau$ in units of $2N_A$ generations. Let $x_1, x_2, x_3$ be the frequencies of haplotypes $AB$, $Ab$, $aB$ and $D = x_1(1 - x_1 - x_2 - x_3) - x_2x_3$ the linkage disequilibrium. The density $\varphi(x_1,x_2,x_3,\tau)$ on the tetrahedron $\{x_i \ge 0,\ \sum_i x_i \le 1\}$ follows the Hill–Robertson forward diffusion

$$\partial_\tau\varphi = \frac{1}{2}\sum_{i=1}^{3}\partial_{x_i}^2\!\left(\frac{x_i(1-x_i)}{\nu(\tau)}\varphi\right) - \sum_{1\le i<j\le 3}\partial_{x_i}\partial_{x_j}\!\left(\frac{x_ix_j}{\nu(\tau)}\varphi\right) + \frac{\rho}{2}\Big[\partial_{x_1}(D\varphi) - \partial_{x_2}(D\varphi) - \partial_{x_3}(D\varphi)\Big],$$

with influx of new pairs whenever a mutation arises at one locus while the other is polymorphic, at rate proportional to $\theta^2$, $\theta = 4N_A\mu$ (two-locus Poisson random field).

**Sample spectrum.** For $n$ sampled haplotypes the expected two-locus spectrum is

$$F_{i,j,k} \propto \iiint \varphi(x_1,x_2,x_3)\binom{n}{i,j,k}x_1^ix_2^jx_3^k(1-x_1-x_2-x_3)^{n-i-j-k}\,dx_1\,dx_2\,dx_3,$$

the expected number of pairs of polymorphic sites with $i$ copies of $AB$, $j$ of $Ab$ and $k$ of $aB$ in the sample.

**Composite likelihood.** Treating pairs of loci in a recombination bin as independent, the observed counts $D_{\rho,i}$ are Poisson with means $M_{\rho,i}$, and over bins centered at $\rho_j$

$$\mathcal{L}(\Theta \mid D) = \prod_j\prod_i \frac{e^{-M_{\rho_j,i}}M_{\rho_j,i}^{D_{\rho_j,i}}}{D_{\rho_j,i}!}.$$

If $\tilde M$ is the model spectrum at $\theta = 1$, the maximum-likelihood mutation rate of a bin is $\hat\theta = \big(\sum_i D_i/\sum_i\tilde M_i\big)^{1/2}$.

## Remarks

The diffusion is the forward equation of the two-locus Wright–Fisher model: multinomial resampling gives the second-order drift terms with covariance $x_i\delta_{ij} - x_ix_j$, and recombination moves haplotype frequencies deterministically toward linkage equilibrium with drift $-\rho D/2$ on $x_1$ and $+\rho D/2$ on $x_2, x_3$, removing $\rho D/2$ per unit time from $AB$ (and from $ab$) and adding it to $Ab$ and $aB$. The square root in $\hat\theta$ arises because $M$ scales as $\theta^2$: one mutation must already be segregating (rate $\propto\theta$) when the second arises (rate $\propto\theta$), and maximizing $\sum_i(-\theta^2\tilde M_i + D_i\log\theta^2)$ gives $\theta^2 = \sum D_i/\sum\tilde M_i$. Because pairs of loci are not independent, parameter uncertainty is estimated with the Godambe information matrix and a genomic block bootstrap. Two-locus statistics carry information on recent demography through linkage disequilibrium that the single-locus spectrum lacks; for unphased data the same approach is applied to two-locus genotype counts.

## Sources

- A. P. Ragsdale and R. N. Gutenkunst, "Inferring demographic history using two-locus statistics", Genetics 206 (2017), 1037–1048, Methods (Equations (1)–(5)), <https://doi.org/10.1534/genetics.117.201251>, PMCID PMC5499162.
- W. G. Hill and A. Robertson, "The effect of linkage on limits to artificial selection", Genetical Research 8 (1966), 269–294, <https://doi.org/10.1017/S0016672300010156>.
