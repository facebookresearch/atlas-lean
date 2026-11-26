# Median clustering minimizes the total one-dimensional earth mover's distance

A clustering of one-dimensional data is a finite set of pairs $\{(p_k, f_k)\}_{k=1}^{K}$ with locations $f_k \in \mathbb{R}$ (cellular prevalences of subclonal lineages) and proportions $p_k \ge 0$, $\sum_k p_k = 1$ (fractions of mutations assigned to each lineage); its cumulative distribution function is $F(x) = \sum_{k : f_k \le x} p_k$. The earth mover's distance between clusterings with CDFs $F_i, F_j$ is

$$\mathrm{EMD}(F_i, F_j) = \int_{-\infty}^{\infty} \lvert F_i(x) - F_j(x) \rvert\, dx .$$

Let $F_1, \dots, F_H$ be the CDFs of $H$ clusterings and let $F^*(x)$ be the $\lceil H/2 \rceil$-th smallest of $F_1(x), \dots, F_H(x)$ (the median for odd $H$, the lower median for even $H$). Then $F^*$ is the CDF of a clustering whose locations lie in the union of the locations of the $F_h$, and for every clustering $G$,

$$\sum_{h=1}^{H} \mathrm{EMD}(F_h, F^*) \le \sum_{h=1}^{H} \mathrm{EMD}(F_h, G).$$

The WeMe consensus then replaces the median clustering by the $K$-constrained median: the clustering with at most $K$ locations minimizing $\mathrm{EMD}(F^*, \cdot)$, found by a grid search over the proportion vector $(p_1, \dots, p_K)$, each location being set to the weighted median of the locations of $F^*$ within the corresponding step of the CDF; outlier reconstructions with the largest EMD to the median clustering are removed first, and $K$ is the ceiling of the median number of clusters of the remaining reconstructions.

## Expansion

For each fixed $x$ the function $y \mapsto \sum_h \lvert F_h(x) - y\rvert$ is minimized by any median of the numbers $F_h(x)$, in particular by $F^*(x)$; integrating this pointwise inequality over $x$ gives the global inequality for every candidate $G$. The order statistic of finitely many nondecreasing right-continuous functions is nondecreasing and right-continuous, it equals $0$ below the smallest location and $1$ above the largest, and it can only jump where some $F_h$ jumps, so $F^*$ is a step CDF supported on the union of the input locations. Because each CDF is a step function, the EMD between two clusterings is a sum of at most $K_i + K_j$ rectangle areas. The median clustering usually has many more clusters than any individual reconstruction, which is why the consensus is projected onto at most $K$ clusters; WeMe uses only the per-lineage summaries $(p_k, f_k)$ and no per-mutation assignments.

## Sources

- S. C. Dentro, I. Leshchiner, K. Haase et al., "Characterizing genetic intra-tumor heterogeneity across 2,658 human cancer genomes", Cell 184 (2021), <https://doi.org/10.1016/j.cell.2021.03.009> (PMC8054914). STAR Methods, subclonal architecture methods and consensus approaches.
