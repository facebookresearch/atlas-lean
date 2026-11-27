# Cellular detection rate

For a single-cell expression matrix with detection indicators $z_{ig} \in \{0,1\}$ over $N$ genes, the cellular detection rate of cell $i$ is the fraction of genes detected in that cell,

$$\mathrm{CDR}_i = \frac{1}{N} \sum_{g=1}^{N} z_{ig} \in [0,1].$$

Here $z_{ig} = 1$ when the measured expression of gene $g$ in cell $i$ exceeds a fixed background threshold (zero, or a conservatively estimated positive threshold), the same threshold for every cell. $\mathrm{CDR}_i$ is a per-cell summary, computable without any model fit, and it is used as a covariate column of the design matrix $X$ in both parts of a two-part model of expression.

## Remarks

Cells differ in volume and hence in total mRNA content, and libraries are diluted to an approximately fixed reaction volume, so the number of distinct species detected varies systematically between cells for reasons unrelated to any treatment. The detected fraction is a proxy for that global scaling, and it carries technical variation (amplification efficiency, viability) along with it. Including $\mathrm{CDR}_i$ as a covariate is the discrete analogue of global normalization: it is estimated jointly with the effects of interest rather than applied as a pre-correction, so no set of control or housekeeping genes is needed. Because $\mathrm{CDR}_i$ is an average over genes, conditioning on it induces dependence between genes within a cell, which is exactly why ignoring it inflates apparent gene-gene correlation.

## Sources

- Finak G, McDavid A, Yajima M, et al. MAST: a flexible statistical framework for assessing transcriptional changes and characterizing heterogeneity in single-cell RNA sequencing data. *Genome Biology* 16:278 (2015), equation (1) and Methods, "Single-cell RNA-seq hurdle model". DOI <https://doi.org/10.1186/s13059-015-0844-5>. PMCID PMC4676162.
