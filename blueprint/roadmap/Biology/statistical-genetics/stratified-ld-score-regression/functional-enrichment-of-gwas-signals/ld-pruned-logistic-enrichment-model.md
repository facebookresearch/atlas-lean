# LD-pruned logistic enrichment model for GWAS signals

**Data.** Start from genome-wide association p-values, a reference panel for linkage disequilibrium $r^2$, binary functional annotations $A_1, \dots, A_m$ (genomic intervals), and each variant's distance to the nearest transcription start site.

1. *LD pruning.* Greedily build an approximately independent variant set: repeatedly keep the most significant remaining variant and discard all variants with $r^2 \ge 0.01$ to it within 1 Mb.
2. *LD tagging.* A kept variant overlaps annotation $A_j$ if it, or any proxy with $r^2 \ge 0.8$ within 500 kb, lies in $A_j$.
3. *Feature matching.* Bin the kept variants into quantiles of TSS distance and of their number of $r^2 \ge 0.8$ proxies, giving categorical covariates $X_{\mathrm{TSS}}$ and $X_{\mathrm{TAGS}}$.

**Model.** For a significance threshold $T$, let $y_i = 1$ if variant $i$ has p-value below $T$ and $y_i = 0$ otherwise. For annotation $j$ fit

$$\mathrm{logit}\, \mathbb{E}(y) = \mathbf{1}\alpha + X_{\mathrm{TSS}} \beta_{\mathrm{TSS}} + X_{\mathrm{TAGS}} \beta_{\mathrm{TAGS}} + X_{A_j} \beta_{A_j}.$$

The enrichment odds ratio is $\mathrm{OR}_{A_j} = e^{\beta_{A_j}}$; testing $\beta_{A_j} = 0$ against $\beta_{A_j} \in \mathbb{R}$ gives the enrichment p-value, with $\beta_{A_j} > 0$ an enrichment and $\beta_{A_j} < 0$ a depletion. Multiple annotations are combined by forward selection: annotations ranked by single-annotation significance are added one at a time if an analysis-of-deviance $\chi^2$ test shows improved fit. Multiple testing is corrected by Bonferroni over an effective number of independent annotations computed from the eigenvalues of the annotation correlation matrix.

## Remarks

Without pruning, a single associated locus contributes many correlated significant variants that all overlap the same element, inflating apparent enrichment; pruning to $r^2 < 0.01$ makes the rows of the regression approximately independent, while tagging at $r^2 \ge 0.8$ keeps credit for a causal variant that was pruned in favor of a correlated lead variant. Variants with many proxies are both more likely to tag an association and more likely to overlap some annotation, and gene-proximal variants are enriched for both too; including these as categorical covariates compares only variants with similar LD and genomic context. On simulated null annotations matched to real peak lengths and spacing, models that ignore LD had false-positive rates of $0.15$–$0.33$ at nominal $0.05$, while the matched model preserved the nominal rate, and the number of LD proxies was the single most important confounder. Unlike stratified LD-score regression, which partitions heritability, this model tests over-representation of threshold-passing loci.

## Sources

- V. Iotchkova, G. R. S. Ritchie, M. Geihs et al., "GARFIELD classifies disease-relevant genomic features through integration of functional annotations with association signals", Nature Genetics 51 (2019), <https://doi.org/10.1038/s41588-018-0322-6>, PMCID PMC6908448. Online Methods, "Data processing", enrichment model and "Multiple testing".
