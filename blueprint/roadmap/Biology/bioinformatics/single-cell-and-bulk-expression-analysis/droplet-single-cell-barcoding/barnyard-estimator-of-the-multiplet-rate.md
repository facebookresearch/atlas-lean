# Barnyard estimator of the multiplet rate

**Poisson loading.** Suppose the number $N$ of cells captured in a droplet partition is Poisson with mean $\lambda > 0$, independently across partitions. Among partitions containing at least one cell, the multiplet fraction is

$$m(\lambda) = \Pr(N \ge 2 \mid N \ge 1) = 1 - \frac{\lambda}{e^{\lambda} - 1}.$$

It is strictly increasing in $\lambda$, with $m(\lambda) = \lambda/2 - \lambda^2/12 + O(\lambda^3)$ as $\lambda \to 0$, so lowering the loading concentration trades throughput for purity.

**Barnyard estimator.** In a two-species mixing experiment, each cell is independently of species A with probability $p \in (0, 1)$ and of species B otherwise. A partition with $j \ge 2$ cells is called mixed when it contains both species, which happens with probability

$$h_j(p) = 1 - p^j - (1-p)^j,$$

and $h_2(p) = 2p(1-p) \le h_j(p)$ for every $j \ge 2$. Let $x$ be the observed fraction of cell barcodes that are mixed. Then

$$\mathbb{E}[x] = \sum_{j \ge 2} \Pr(N = j \mid N \ge 1)\, h_j(p) \;\ge\; 2p(1-p)\, m,$$

with equality exactly when no partition holds three or more cells. Hence $\hat m = x / (2p(1-p))$ is unbiased for the multiplet rate when multiplets are doublets and biased upward otherwise. For an equal mixture, $p = 1/2$, the estimator is $\hat m = 2x$: the multiplet rate is twice the rate of mixed-species barcodes.

## Remarks

$\Pr(N \ge 1) = 1 - e^{-\lambda}$ and $\Pr(N = 1) = \lambda e^{-\lambda}$ give $m(\lambda)$ directly. The function $\lambda/(e^\lambda - 1)$ is strictly decreasing on $(0, \infty)$ with Taylor series $1 - \lambda/2 + \lambda^2/12 - \cdots$, which gives the monotonicity and the small-$\lambda$ expansion. A doublet is homotypic with probability $p^2 + (1-p)^2$, so only the fraction $2p(1-p)$ of doublets is visible as mixed; since $p^j$ and $(1-p)^j$ decrease in $j$, larger multiplets are at least as visible, which is why the estimator can only overcount. In the 10x Genomics GemCode system, gel beads fill about 80% of partitions and Poisson loading of cells then gives a cell capture rate of about 50%; the multiplet rate in human–mouse mixtures was defined as twice the rate of barcodes with significant UMI counts from both species.

## Sources

- G. X. Y. Zheng et al., "Massively parallel digital transcriptional profiling of single cells", Nature Communications 8 (2017), 14049, Discussion and Methods (section "Alignment, barcode assignment and UMI counting"), <https://doi.org/10.1038/ncomms14049>, PMCID: PMC5241818.
