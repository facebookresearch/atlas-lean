# Size-factor scaling and the log(x+1) transform of single-cell counts

Let $C = (c_{ij})$ be a count matrix with cells $i = 1, \dots, n$ and genes $j = 1, \dots, g$, where $c_{ij} \in \mathbb{N}$ is the number of unique molecules of gene $j$ observed in cell $i$, and let $d_i = \sum_{j=1}^{g} c_{ij}$ be the count depth of cell $i$.

**Definition (global scaling normalization).** A size factor is a positive number $s_i$ per cell, and the normalized expression is $\tilde c_{ij} = c_{ij} / s_i$. Count-depth scaling takes $s_i = d_i / K$ for a constant $K$ and requires $d_i > 0$ (with $K = 10^6$ this is counts per million, with $K = \operatorname{median}_i d_i$ the median-depth convention). The high-count filtered variant uses one retained gene set for all cells, excluding every gene that carries at least $5\%$ of the counts of some cell,

$$G = \{\, j : c_{ij} < 0.05\, d_i \text{ for every cell } i \,\},$$

and sets $s_i \propto \sum_{j \in G} c_{ij}$, which requires this retained depth to be positive for every cell. Pooling-based estimation instead fits the $s_i$ by regression on summed profiles of pools of cells, which is consistent as long as fewer than half the genes are differentially expressed between cells.

**Definition (log transform).** The normalized matrix is then mapped entrywise by $x \mapsto \log(x + 1)$.

**Properties.** Global scaling is a strictly positive rescaling of each row, so it preserves the zero pattern of the matrix: $\tilde c_{ij} = 0$ iff $c_{ij} = 0$, and the same holds after the log transform, since $\log(0 + 1) = 0$. Differences of log-transformed values are log ratios, $\log(\tilde c_{ij} + 1) - \log(\tilde c_{i'j} + 1) = \log\frac{\tilde c_{ij} + 1}{\tilde c_{i'j} + 1}$, so distances in the transformed space measure fold changes; the offset $1$ keeps the transform finite at zero counts. The transform damps, without removing, the mean–variance dependence of count data, and reduces right skew.

## Remarks

The model behind count-depth scaling is that cells contained comparable numbers of mRNA molecules and that the observed depth differences arise from the sampling inherent in capture, reverse transcription and sequencing; under that model dividing by depth restores comparable relative abundances. The assumption fails when cells genuinely differ in total RNA content, which is what motivates excluding dominating genes from the depth, or estimating size factors from pools. Two cautions are worth stating precisely. First, scaling is a per-cell operation and therefore cannot remove gene-level or batch-level effects, which is why normalization is kept separate from correction. Second, the log transform is not variance stabilizing for these data, and where size-factor distributions differ systematically between compared groups it can create apparent differential expression; the transformed data are a working representation, not a distributional model. Scaling genes to zero mean and unit variance is a separate, optional choice that weights all genes equally and discards expression magnitude as a proxy for relevance.

## Sources

- M. D. Luecken and F. J. Theis, "Current best practices in single-cell RNA-seq analysis: a tutorial", Molecular Systems Biology 15 (2019), e8746, "Normalization" and "Stages of pre-processed data" sections, <https://doi.org/10.15252/msb.20188746>, PMCID: PMC6582955.
- A. T. L. Lun, K. Bach and J. C. Marioni, "Pooling across cells to normalize single-cell RNA sequencing data with many zero counts", Genome Biology 17 (2016), 75.
