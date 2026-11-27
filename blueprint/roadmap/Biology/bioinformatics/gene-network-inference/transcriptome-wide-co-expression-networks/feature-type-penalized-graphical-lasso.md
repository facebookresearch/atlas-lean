# Feature-type-penalized graphical lasso for transcription and splicing networks

For each gene in an RNA-seq dataset, compute its total expression (TE) and the isoform ratios (IR) of its isoforms, the abundance of each isoform divided by the gene's total, dropping each gene's least abundant isoform to avoid the linear dependency $\sum \mathrm{IR} = 1$. After normalization, let $S$ be the sample covariance matrix of all TE and IR features. For a feature $r$ let $\operatorname{gene}(r)$ be its gene and $\operatorname{type}(r) \in \{\mathrm{TE}, \mathrm{IR}\}$ its type. The **transcriptome-wide network** is the support of the estimated precision matrix

$$\hat\Theta = \arg\min_{\Theta \succ 0}\; -\log\det\Theta + \operatorname{tr}(S\Theta) + \|\Lambda \circ \Theta\|_1,$$

where $\circ$ is the elementwise product, $\|\cdot\|_1$ the elementwise $\ell_1$ norm, and the penalty matrix depends on the feature types:

$$\Lambda_{rc} = \begin{cases} \lambda_d & r = c, \\ \lambda_s & r \ne c,\ \operatorname{gene}(r) = \operatorname{gene}(c), \\ \lambda_{tt} & \operatorname{gene}(r) \ne \operatorname{gene}(c),\ \operatorname{type}(r) = \operatorname{type}(c) = \mathrm{TE}, \\ \lambda_{ti} & \operatorname{gene}(r) \ne \operatorname{gene}(c),\ \{\operatorname{type}(r), \operatorname{type}(c)\} = \{\mathrm{TE}, \mathrm{IR}\}, \\ \lambda_{ii} & \operatorname{gene}(r) \ne \operatorname{gene}(c),\ \operatorname{type}(r) = \operatorname{type}(c) = \mathrm{IR}. \end{cases}$$

An edge joins features $r \ne c$ when $\hat\Theta_{rc} \ne 0$. TE–TE edges indicate co-regulated transcription, TE–IR edges indicate a gene whose expression level is associated with another gene's splicing (for example a splicing factor and its target), and IR–IR edges indicate co-regulated splicing.

## Expansion

The objective is the negative Gaussian log-likelihood of a precision matrix plus a weighted lasso penalty; a zero entry of $\Theta$ means conditional independence of the two features given all others in a Gaussian model, so edges are partial rather than marginal correlations. Using isoform ratios instead of isoform-level expression matters because transcriptional regulation changes all isoform levels of a gene together, while splicing regulation changes their proportions; a network on isoform expression levels would confound the two mechanisms. Separate penalties let the densities of the three edge classes be tuned independently despite their very different numbers of candidate pairs. Saha et al. leave the diagonal unpenalized ($\lambda_d = 0$), use a small penalty $\lambda_s = 0.05$ between features of the same gene, choose $\lambda_{tt}, \lambda_{ti}, \lambda_{ii}$ to give a scale-free topology, and fit per-tissue networks for 16 GTEx tissues with a scalable graphical lasso solver; network hubs were strongly enriched for splicing and RNA-binding genes.

## Sources

- A. Saha, Y. Kim, A. D. H. Gewirtz, et al., "Co-expression networks reveal the tissue-specific regulation of transcription and splicing", Genome Research 27 (2017), 1843–1858, <https://doi.org/10.1101/gr.216721.116> (PMC5668942), Methods "Per-tissue Transcriptome-Wide Networks", Equations (1)–(2).
- J. Friedman, T. Hastie, R. Tibshirani, "Sparse inverse covariance estimation with the graphical lasso", Biostatistics 9 (2008), 432–441, <https://doi.org/10.1093/biostatistics/kxm045>.
