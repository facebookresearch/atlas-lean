# TreeMix composite likelihood

Let $\hat x_{si}$ be the sample allele frequency at SNP $s = 1, \dots, S$ in population $i = 1, \dots, m$, and $\bar x_s = \frac1m\sum_i \hat x_{si}$. The sample covariance relative to the mean population is

$$\hat W_{ij} = \frac1S\sum_{s=1}^S (\hat x_{si} - \bar x_s)(\hat x_{sj} - \bar x_s).$$

Finite sampling adds a variance $B_i$ to each $\hat x_{si}$ about the population frequency (estimated, for $n_i$ sampled gene copies, by $B_i = \frac1S\sum_s \hat x_{si}(1 - \hat x_{si})/(n_i - 1)$). Because the frequencies are centred by $C = I_m - \frac1m\mathbf 1\mathbf 1^{\top}$, the resulting bias of $\hat W$ is the full matrix $C\operatorname{diag}(B_1, \dots, B_m)\,C$, with entries

$$\big(C\operatorname{diag}(B)\,C\big)_{ij} = B_i\,[i = j] - \frac{B_i + B_j}{m} + \frac{1}{m^2}\sum_{k=1}^m B_k ,$$

not a diagonal matrix: even when every $B_i = B > 0$, each off-diagonal entry is $-B/m$. The sampling-corrected estimate subtracts this whole matrix from $\hat W$ before fitting; below $\hat W$ denotes the corrected estimate. Split the genome into $K$ blocks of contiguous SNPs longer than the scale of linkage disequilibrium, compute $\hat W_{ij}$ in each block, and let $\hat s_{ij}$ be the resulting block-resampling standard error of $\hat W_{ij}$. For a population graph $G$ (a rooted directed acyclic graph with branch lengths and mixture weights) let $W(G)$ be its predicted [mean-centred covariance](treemix-mean-centred-covariance.md). TreeMix maximizes the composite likelihood

$$\mathcal L(G) = \prod_{1 \le i \le j \le m} \frac{1}{\hat s_{ij}\sqrt{2\pi}} \exp\!\left[-\frac{\big(\hat W_{ij} - W_{ij}(G)\big)^2}{2\hat s_{ij}^2}\right]$$

over branch lengths and mixture weights for each topology, starting from a maximum-likelihood tree and adding migration edges between populations with large residuals $\hat W_{ij} - W_{ij}(G)$.

## Depends on

- [TreeMix covariance relative to the mean population](treemix-mean-centred-covariance.md)

## Proof depends on

None: the page defines the sampling-corrected covariance estimate and the composite likelihood; the bias matrix is the centring identity $W = CVC$ applied to the sampling noise, as the Expansion describes.

## Expansion

Averaged over many independent genomic blocks, each $\hat W_{ij}$ is approximately normal about $W_{ij}$ by the central limit theorem; the block resampling inflates the naive per-SNP standard error to account for linkage disequilibrium. Multiplying the marginal normal densities ignores correlations among the entries, which avoids the matrix inversions of a Wishart likelihood but means the product is a composite likelihood, so significance of migration edges is assessed by block resampling rather than likelihood-ratio tests. Sampling noise in population $i$ is independent across populations with variance $B_i$, so its covariance is $\operatorname{diag}(B)$, and centring maps it to $C\operatorname{diag}(B)\,C$ exactly as it maps the drift covariance $V$ to $W = CVC$. In the tree model the root position is not identifiable. Results, "Estimation from finite samples and many SNPs", Equations (24)–(28).

## Sources

- J. K. Pickrell, J. K. Pritchard, "Inference of Population Splits and Mixtures from Genome-Wide Allele Frequency Data", PLoS Genetics 8 (2012), e1002967, <https://doi.org/10.1371/journal.pgen.1002967> (PMC3499260); Text S1, Equations (6)–(8), <https://doi.org/10.1371/journal.pgen.1002967.s016>.
