# Plate-effect model and summation over cells

**Model.** Let $Y_{ijkg}$ be the read count of gene $i$ in cell $j = 1, \dots, n_{kg}$ of plate $k$ in group $g$. Let $\delta_{ikg} > 0$ be a gene- and plate-specific effect, drawn independently for each plate from a distribution with $\mathbb{E}[\delta_{ikg}] = 1$ and $\mathrm{Var}(\delta_{ikg}) = v_\delta > 0$, and $\theta_{jkg} > 0$ a cell-specific bias (library size, composition) with $\mathbb{E}[\theta_{jkg}] = 1$, the $\theta_{jkg}$ being independent across cells and plates and independent of $\delta$. Given $\delta$ and $\theta$, counts are independent across genes and cells with

$$\mathbb{E}(Y_{ijkg} \mid \delta_{ikg}, \theta_{jkg}) = \delta_{ikg}\, \theta_{jkg}\, \mu_{ig},$$

where $\mu_{ig}$ is the expected count of gene $i$ in group $g$. The null hypothesis of no differential expression for gene $i$ is that $\mu_{ig}$ does not depend on $g$.

**Proposition.**

1. *(Within-plate correlation.)* For two distinct cells $j \ne j'$ on the same plate,

$$\mathrm{Cov}(Y_{ijkg}, Y_{ij'kg}) = \mu_{ig}^2\, v_\delta > 0,$$

while counts on different plates are independent. Cells are therefore not independent replicates, and a model treating them as such underestimates the variance of group means.
2. *(Plate sums.)* The plate sums $Z_{ikg} = \sum_{j} Y_{ijkg}$ are independent across plates, with $\mathbb{E}[Z_{ikg}] = n_{kg}\, \mu_{ig}$; the expected log-fold change between groups computed from plate sums (normalized by cell numbers or library sizes) equals the one computed from cells, so summation changes the variance model, not the effect being tested.
3. *(Variance reduction.)* If, given $\delta_{ikg}$, the cell counts are i.i.d. negative binomial with mean $m$ and dispersion $\phi$ (variance $m + \phi m^2$), the sum of $n$ of them has conditional variance $n m + n \phi m^2$ and squared coefficient of variation $\frac{1}{n m} + \frac{\phi}{n}$, which tends to $0$; relative to its mean, the plate sum is far less noisy than a single cell.

No rescaling by a single factor per cell can remove $\delta_{ikg}$, because it differs across genes.

## Expansion

For part 1, condition on $(\delta, \theta)$: conditional independence makes the conditional covariance zero, so the covariance equals the covariance of the conditional means, $\mu^2\, \mathrm{Cov}(\delta \theta_j, \delta \theta_{j'}) = \mu^2 (\mathbb{E}[\delta^2]\, \mathbb{E}[\theta_j]\, \mathbb{E}[\theta_{j'}] - 1) = \mu^2 v_\delta$, using that $\theta_j$, $\theta_{j'}$ and $\delta$ are mutually independent. (If instead $\theta_j = \theta_{j'}$ with variance $v_\theta$, the covariance would be $\mu^2((1 + v_\delta)(1 + v_\theta) - 1)$.) Independence across plates likewise uses that plate effects and cell biases are drawn independently for different plates. Part 2 follows from independence of plate effects and linearity of expectation. Part 3 is additivity of variances for conditionally independent summands. In simulations with three plates per group and log-normal plate effects, edgeR, DESeq2, voom, Monocle, MAST and negative binomial mixed models applied to single cells all exceeded the nominal type I error; analysing plate sums with bulk methods restored near-nominal error control (residual liberalness for edgeR and DESeq2 because sums are not exactly negative binomial) without loss of detection power, since information sharing across genes compensates for the fewer residual degrees of freedom.

## Sources

- A. T. L. Lun and J. C. Marioni, "Overcoming confounding plate effects in differential expression analyses of single-cell RNA-seq data", Biostatistics 18 (2017), Sections 2.1 and 3, <https://doi.org/10.1093/biostatistics/kxw055> (PMC5862359).
