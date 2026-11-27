# Poisson-gamma posterior segmentation with Kolmogorov-Smirnov breakpoints

Order genes by genomic position and partition them into consecutive windows (initially $25$ genes each). In window $i$, model the back-transformed counts $y_{i1}, \dots, y_{in_i}$ as

$$y_{ik} \mid \lambda_i \sim \mathrm{Poisson}(\lambda_i) \ \text{independently}, \qquad \lambda_i \sim \mathrm{Gamma}(\alpha, \beta) \ (\text{shape } \alpha,\ \text{rate } \beta).$$

By conjugacy the posterior is

$$\lambda_i \mid y_{i\cdot} \sim \mathrm{Gamma}\Bigl(\alpha + \sum_{k} y_{ik},\ \beta + n_i\Bigr), \qquad \mathbb{E}[\lambda_i \mid y_{i\cdot}] = \frac{\alpha + \sum_k y_{ik}}{\beta + n_i}.$$

Draw $1000$ posterior samples of $\lambda_i$ for each window, with empirical distribution function $F_i$. For adjacent windows $i$ and $j$ compute the two-sample Kolmogorov-Smirnov statistic

$$D_{ij} = \sup_{x} \bigl| F_i(x) - F_j(x) \bigr|,$$

and declare a copy-number breakpoint between them when $D_{ij}$ exceeds a cutoff; otherwise the windows are joined. If fewer than $25$ breakpoints are found, the cutoff is halved, at most twice. Breakpoints found in each cell cluster are pooled into consensus breakpoints, the posterior mean of every resulting segment is computed in every cell, and the log-transformed, centered segment means give each cell's relative copy-number profile.

## Depends on

- [Freeman-Tukey variance-stabilizing transform for Poisson counts](freeman-tukey-variance-stabilizing-transform-for-poisson-counts.md)

## Remarks

The gamma prior shrinks window means toward a common level, which damps the noise of sparse single-cell counts, and conjugacy makes the posterior exact and cheap. Comparing whole posterior distributions rather than point estimates lets the Kolmogorov-Smirnov distance account for the uncertainty of each window. Adaptive halving of the cutoff guards against under-segmentation in cells with few detected genes. With a median gene spacing of about $24.5$ kb and roughly $12.5\%$ of genes detected, a $25$-gene window corresponds to a resolution of about $5$ Mb.

## Sources

- R. Gao et al., "Delineating copy number and clonal substructure in human tumors from single-cell transcriptomes", Nature Biotechnology 39 (2021) 599-608, Methods, "Copy number segmentation" and "Theoretical estimation of genomic copy number resolution". <https://doi.org/10.1038/s41587-020-00795-2> (PMC8122019)
