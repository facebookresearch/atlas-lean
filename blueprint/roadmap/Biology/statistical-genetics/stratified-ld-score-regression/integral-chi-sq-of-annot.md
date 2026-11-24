# Stratified LD-score regression

Let a [stratified LD-score model](model.md) on a measure $\mu$ have $N \ne 0$ individuals, let $\mathcal{C}$ be a finite set of annotations with values $a_{kC} \in \mathbb{R}$ and coefficients $\tau_C \in \mathbb{R}$ such that $\sigma^2_k = \sum_{C \in \mathcal{C}} \tau_C\, a_{kC}$ for every marker $k$, and let $X$ be a [standardized](../ld-score-regression/is-standardized.md) real $N \times M$ genotype matrix. Then for every marker $j$ (Finucane et al. 2015; continuous annotations, Gazal et al. 2017),

$$\int \chi^2_j \, d\mu = N \sum_{C \in \mathcal{C}} \tau_C\, \ell(j, C) + \sigma^2_e,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $\ell$ the [annotation LD score](annot-ldscore.md).

## Sources

- H. K. Finucane, B. Bulik-Sullivan, A. Gusev, G. Trynka, Y. Reshef, P.-R. Loh, et al., *Partitioning heritability by functional annotation using genome-wide association summary statistics*, Nat. Genet. 47 (2015), 1228–1235.
- S. Gazal, H. K. Finucane, N. A. Furlotte, P.-R. Loh, P. F. Palamara, X. Liu, et al., *Linkage disequilibrium–dependent architecture of human complex traits shows action of negative selection*, Nat. Genet. 49 (2017), 1421–1427.
