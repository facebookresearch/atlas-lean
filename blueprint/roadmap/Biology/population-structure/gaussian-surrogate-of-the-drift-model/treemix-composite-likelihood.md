# TreeMix composite likelihood

Let $\hat x_{si}$ be the sample allele frequency at SNP $s = 1, \dots, S$ in population $i = 1, \dots, m$, and $\bar x_s = \frac1m\sum_i \hat x_{si}$. The sample covariance relative to the mean population is

$$\hat W_{ij} = \frac1S\sum_{s=1}^S (\hat x_{si} - \bar x_s)(\hat x_{sj} - \bar x_s),$$

with its diagonal corrected for the extra drift contributed by finite sampling. Split the genome into $K$ blocks of contiguous SNPs longer than the scale of linkage disequilibrium, compute $\hat W_{ij}$ in each block, and let $\hat s_{ij}$ be the resulting block-resampling standard error of $\hat W_{ij}$. For a population graph $G$ (a rooted directed acyclic graph with branch lengths and mixture weights) let $W(G)$ be its predicted [mean-centred covariance](treemix-mean-centred-covariance.md). TreeMix maximizes the composite likelihood

$$\mathcal L(G) = \prod_{1 \le i \le j \le m} \frac{1}{\hat s_{ij}\sqrt{2\pi}} \exp\!\left[-\frac{\big(\hat W_{ij} - W_{ij}(G)\big)^2}{2\hat s_{ij}^2}\right]$$

over branch lengths and mixture weights for each topology, starting from a maximum-likelihood tree and adding migration edges between populations with large residuals $\hat W_{ij} - W_{ij}(G)$.

## Depends on

- [TreeMix covariance relative to the mean population](treemix-mean-centred-covariance.md)
- [The qpGraph score S1](../fitting-admixture-graphs-by-least-squares/score-s1.md)

## Expansion

Averaged over many independent genomic blocks, each $\hat W_{ij}$ is approximately normal about $W_{ij}$ by the central limit theorem; the block resampling inflates the naive per-SNP standard error to account for linkage disequilibrium. Multiplying the marginal normal densities ignores correlations among the entries, which avoids the matrix inversions of a Wishart likelihood but means the product is a composite likelihood, so significance of migration edges is assessed by block resampling rather than likelihood-ratio tests. In the tree model the root position is not identifiable. Results, "Estimation from finite samples and many SNPs", Equations (24)–(28).

## Sources

- J. K. Pickrell, J. K. Pritchard, "Inference of Population Splits and Mixtures from Genome-Wide Allele Frequency Data", PLoS Genetics 8 (2012), e1002967, <https://doi.org/10.1371/journal.pgen.1002967> (PMC3499260).
