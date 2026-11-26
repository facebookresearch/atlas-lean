# Permutation threshold for the maximum statistic of a genome scan

Let $y = (y_1, \dots, y_n)$ be the trait values of $n$ individuals and $G$ their marker genotypes, with the genotype data of individual $i$ kept together as one unit $G_i$. A genome scan computes a test statistic $T_\ell(y, G)$ (for example a LOD score) at each analysis position $\ell$ in a finite set $L$ and summarizes the scan by the genome-wide maximum

$$T^{\max}(y, G) = \max_{\ell \in L} T_\ell(y, G).$$

For a permutation $\pi$ of $\{1, \dots, n\}$ write $y_\pi = (y_{\pi(1)}, \dots, y_{\pi(n)})$: the trait values are shuffled among individuals while every individual's marker data stay intact, so linkage and linkage disequilibrium among markers are preserved and only the trait–genotype association is broken.

Draw permutations $\pi_1, \dots, \pi_M$ independently and uniformly at random and record $T^{\max}_m = T^{\max}(y_{\pi_m}, G)$. The empirical genome-wide threshold at level $\alpha \in (0, 1)$ is the $100(1 - \alpha)$ percentile of $T^{\max}_1, \dots, T^{\max}_M$; a position $\ell$ is declared significant when $T_\ell(y, G)$ exceeds it. A single threshold applies to every position, so the procedure controls the experiment-wise (genome-wide) rather than the per-position error rate.

## Expansion

The statistic $T^{\max}$ automatically accounts for the number of positions tested, the correlation between nearby positions, marker density, missing genotypes and the actual (possibly non-normal) trait distribution, because each permuted data set is analyzed by exactly the same scan as the observed one. No analytic null distribution for correlated test statistics is needed.

## Sources

- G. A. Churchill and R. W. Doerge, "Empirical threshold values for quantitative trait mapping", Genetics 138 (1994), 963–971, <https://doi.org/10.1093/genetics/138.3.963> (PMC1206241).
