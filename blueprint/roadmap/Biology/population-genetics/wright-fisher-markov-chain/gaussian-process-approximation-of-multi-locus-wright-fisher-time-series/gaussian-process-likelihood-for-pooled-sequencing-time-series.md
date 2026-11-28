# Gaussian-process likelihood for pooled-sequencing time series

In an evolve-and-resequence experiment, $R$ replicate populations founded from a known haplotype configuration $G_0$ evolve under the multi-locus [Wright–Fisher model](../wright-fisher.md) with parameters $\theta$ (effective size, selection coefficient and dominance at a candidate site, recombination rates). At generations $t_1,\dots,t_T$ and biallelic loci $1,\dots,L$, pooled sequencing reports read counts $D_{ijk}$ of allele $A_1$ out of coverage $c_{ijk}$ (generation $i$, locus $j$, replicate $k$). Let $X_{ijk} \in [0,1]$ be the unobserved population frequency of $A_1$. If, given $X$, each site is sampled independently and binomially, $D_{ijk} \sim \mathrm{Binomial}(c_{ijk}, X_{ijk})$, then

$$\mathcal{L}(D\mid\theta) = \int_{[0,1]^{T\times L\times R}} \prod_{i,j,k}\binom{c_{ijk}}{D_{ijk}} x_{ijk}^{D_{ijk}}(1-x_{ijk})^{c_{ijk}-D_{ijk}}\; p_X(x\mid\theta)\,dx .$$

The exact $p_X$ requires summing over all genotype configurations of the population at every generation. The Gaussian-process approximation replaces it by

$$X \mid G_0,\theta \sim \mathcal{N}\bigl(\mu(G_0,\theta), \Sigma(G_0,\theta)\bigr),$$

whose mean entries $\mathrm{E}X_{ij}$ and covariances $\mathrm{cov}(X_{ij}, X_{uv})$ are computed from one- and two-locus Wright–Fisher models, replicates being independent and identically distributed. The resulting approximate likelihood $\tilde{\mathcal{L}}(D\mid\theta)$, the same integral with the Gaussian density $\phi_\theta$ in place of $p_X$, keeps the exact first two moments, including linkage-induced covariance across loci and across generations, and drops higher-order correlations. For deep coverage the binomial factors concentrate at the observed frequencies, so $\tilde{\mathcal{L}}(D\mid\theta) \propto \phi_\theta(D/c)$ approximately and no integral is needed. Maximizing $\tilde{\mathcal{L}}$ gives estimates and likelihood-ratio tests of selection, dominance, effective size and local recombination rate.

## Depends on

- [Neutral Wright–Fisher transition matrix](../wright-fisher.md)
- [Drift-corrected haplotype moments in the two-locus Wright–Fisher model](drift-corrected-haplotype-frequency-moments-in-the-two-locus-wright-fisher-model.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

Each marginal frequency is a linear combination of haplotype frequencies, so its mean and covariance involve at most two loci and can be obtained by marginalizing the other loci out of the multi-locus chain. For neutral loci the two-locus moments are explicit to first order in $r$ and $1/(2N)$; near a selected site the authors linearize the drift around the deterministic selection trajectory $\bar X_t = f(\bar X_{t-1})$ with $f(x) = x + s[h + (1-2h)x]x(1-x)/(1 + sx[2h + (1-2h)x])$. Unlike a diffusion approximation, the moment recursion stays accurate for small $N$ and few generations, the regime of laboratory experiments.

## Sources

- J. Terhorst, C. Schlötterer and Y. S. Song, "Multi-locus analysis of genomic time series data from experimental evolution", PLoS Genetics 11 (2015), e1005069, <https://doi.org/10.1371/journal.pgen.1005069>, PMCID PMC4388667. Eqs. (1)–(4) and (10), and Methods.
