# Poisson excess-mutation test for driver regulatory elements

**Setting.** Candidate regulatory elements (DNase I hypersensitive sites) are tested for an excess of somatic point mutations over the local neutral expectation. Elements are first grouped by $k$-means clustering, per chromosome, on five standardized covariates of local mutation rate: replication timing, open or closed chromatin status, GC content, local gene density, and the trinucleotide-content expectation. For element $i$ let $n_{i, t}$ be the number of occurrences of trinucleotide $t$ in it; with $M_t$ mutations observed genome-wide at trinucleotide $t$ and $N_t$ occurrences of $t$ in the genome, that last covariate is

$$\mu_i = \sum_{t} \frac{n_{i, t} M_t}{N_t}. \tag{1}$$

**Statement** (D'Antonio et al. 2017, Methods, eqs. (1)–(4)). Within a cluster the per-nucleotide neutral mutation probability $\mu$ is taken to be constant, so for an element of repeat-masked length $L$ the mutation count is $n \sim \mathrm{Poisson}(\lambda)$, $\lambda = \mu L$, under neutrality. The cluster's rate is estimated by maximum likelihood from its $N$ elements,

$$\hat\mu = \frac{\sum_{i=1}^{N} n_i}{\sum_{i=1}^{N} L_i}, \tag{2}$$

and the test statistic of an element with $n$ mutations is the upper Poisson tail

$$p = 1 - \sum_{k=0}^{n-1} \frac{\hat\lambda^k}{k!} e^{-\hat\lambda}, \qquad \hat\lambda = \hat\mu L. \tag{3}$$

Because $n$ is discrete, the null distribution of $p$ is not uniform; it is obtained by simulating counts $n_i \sim \mathrm{Poisson}(\hat\mu_i L_i)$ for every element. With $F_{\mathrm{exp}}$ and $F_{\mathrm{obs}}$ the cumulative distribution functions of the simulated and observed $p$ values, the false discovery rate at threshold $p^*$ is

$$\mathrm{FDR}(p^*) = \frac{F_{\mathrm{exp}}(p^*)}{F_{\mathrm{obs}}(p^*)}. \tag{4}$$

## Depends on

- [Pooled Poisson rate](../../../Probability/statistical-estimation/existence-and-uniqueness-of-the-gamma-poisson-ml/pooled-mean.md)

## Remarks

The estimator (2) pools all elements of a cluster, including any that are under selection, so $\hat\mu$ exceeds the true neutral rate whenever the cluster contains drivers; a larger $\hat\lambda$ makes an observed count less extreme, so (3) overestimates the $p$ value of a driver and the test is conservative. The clustering is what makes a single $\mu$ per cluster defensible: somatic mutation density varies several-fold with replication timing and chromatin state, and comparing an element against the genome average rather than against elements of matched covariates would produce excesses wherever the background is high. Equation (4) is the empirical-null form of the false discovery rate: since the Poisson null puts an atom at $p = 1$ and no mass between the attainable tail values, the theoretical uniform null does not apply and the simulated $F_{\mathrm{exp}}$ replaces it.

## Sources

- M. D'Antonio, D. Weghorn, A. D'Antonio-Chronowska, F. Coulet, K. M. Olson, C. DeBoever et al., "Identifying DNase I hypersensitive sites as driver distal regulatory elements in breast cancer", Nature Communications 8 (2017), 436, Methods ("Identification of significantly mutated breast DHSs in Filter 1", "Inference of mutation probability", "Test statistic p", "False discovery rate"), eqs. (1)–(4), <https://doi.org/10.1038/s41467-017-00100-x>, PMCID PMC5585396.
