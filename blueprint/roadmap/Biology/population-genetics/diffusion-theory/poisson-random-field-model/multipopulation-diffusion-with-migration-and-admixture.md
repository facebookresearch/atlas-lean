# Multi-population diffusion for the joint allele-frequency density

Consider $P$ populations under Wright–Fisher reproduction and infinitely-many-sites mutation. Let $\phi(x_1, \dots, x_P, \tau)$, $x_i \in [0,1]$, be the density of derived mutations at relative frequencies $x_i$ in population $i$, with time $\tau = t/(2N_{\mathrm{ref}})$ ($t$ in generations). Write $\nu_i = N_i/N_{\mathrm{ref}}$ for relative effective sizes, $\gamma_i = 2N_{\mathrm{ref}} s_i$ for scaled selection coefficients, and $M_{i \leftarrow j} = 2N_{\mathrm{ref}} m_{i \leftarrow j}$ for scaled conservative migration rates, $m_{i \leftarrow j}$ being the fraction of chromosomes in population $i$ that are new migrants from $j$ each generation. Then

$$\frac{\partial \phi}{\partial \tau} = \frac12 \sum_{i=1}^P \frac{\partial^2}{\partial x_i^2}\Bigl[ \frac{x_i(1-x_i)}{\nu_i}\, \phi \Bigr] - \sum_{i=1}^P \frac{\partial}{\partial x_i}\Bigl[ \Bigl( \gamma_i x_i (1 - x_i) + \sum_{j=1}^P M_{i \leftarrow j}(x_j - x_i) \Bigr) \phi \Bigr],$$

with no-flux boundaries except at the corners where all $x_i = 0$ or all $x_i = 1$ (loss and fixation), and new mutations injected at low frequency at a rate proportional to the population-scaled mutation flux $\theta$. The diffusion approximation assumes large $N$ with $m$ and $s$ of order $1/N$.

Demographic events act on the dimension of $\phi$:

- **Admixture.** A new population $P+1$ formed from populations $i$ and $j$ in proportions $f$ and $1 - f$ has

$$\phi(x_1, \dots, x_P, x_{P+1}) = \phi(x_1, \dots, x_P)\, \delta\bigl(x_{P+1} - [f x_i + (1 - f) x_j]\bigr).$$

- **Split.** A split of population $i$ is the case $f = 1$, $x_{P+1} = x_i$.
- **Removal.** Dropping population $k$ marginalizes: $\phi \mapsto \int_0^1 \phi\, dx_k$.

For $P = 1$ and constant parameters, the stationary solution is the one-population [Poisson random field density](prf-density.md).

## Depends on

- [Sawyer–Hartl Poisson random field density](prf-density.md)

## Proof depends on

Its proof is the diffusion limit of the per-generation moments and linearity of expectation, as the Expansion describes.

## Expansion

Conditional on the current frequencies, the next generation's frequencies in different populations are independent binomial draws after migration. So each coordinate gets drift variance $x_i(1-x_i)/(2N_i)$ per generation and mean change $s_i x_i(1-x_i) + \sum_j m_{i\leftarrow j}(x_j - x_i)$. Rescaling time by $2N_{\mathrm{ref}}$ gives the Kolmogorov forward equation above for the frequency density of a single site. The density $\phi$ of derived mutations is the expected number of sites per unit frequency volume; since each site follows the same forward equation and expectation is linear, $\phi$ obeys the same linear equation, with a mutation source near $x = 0$ supplying new sites. This needs no independence between sites: infinitely many sites only rules out a site mutating twice, and sites on a nonrecombining segment still share one genealogy. Only under the additional assumption that sites are unlinked (independent genealogies) is $\phi$ the intensity of a Poisson random field, with independent Poisson counts per frequency class; for linked sites the counts are dependent and a likelihood built from that product is composite.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, *Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data*, PLoS Genet. 5 (2009), e1000695, <https://doi.org/10.1371/journal.pgen.1000695>, PMCID PMC2760211, Methods, "Diffusion approximation": Equation 1 (diffusion equation) and Equation 2 (admixture).
