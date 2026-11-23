# Haseman–Elston estimator

For a real $N \times N$ matrix $A$ (in the application, the
[genetic relationship matrix](grm.md)) and a vector $y \in \mathbb{R}^N$ of phenotypes, the
Haseman–Elston (cross-product) estimator is

$$\hat h^2 = \frac{\sum_{i<j} A_{ij}\, y_i y_j}{\sum_{i<j} A_{ij}^2},$$

where both sums run over the [pairs](../../bioinformatics/sequence-alignment/multiple-sequence-alignment/pair-finset.md) $i < j$; only the entries of $A$ above the
diagonal enter. If these entries are not all $0$, $\hat h^2$ is the unique least-squares slope,
through the origin, of the cross-products $y_i y_j$ on the entries $A_{ij}$: it
[minimizes the residual sum of squares](he-rss-he-estimate-le.md), and
[no other slope does](he-rss-eq-he-rss-he-estimate-iff.md). If $\sum_{i<j} A_{ij}^2 = 0$, that
is, every $A_{ij}$ with $i < j$ is $0$ (for instance when $N \le 1$), then $\hat h^2 = 0$ by the
convention $x/0 = 0$; every slope then has the same residual sum of squares.

## Sources

- J. K. Haseman, R. C. Elston, *The investigation of linkage between a quantitative trait and a
  marker locus*, Behav. Genet. 2 (1972), 3–19.
- J. Yang, J. Zeng, M. E. Goddard, N. R. Wray, P. M. Visscher, *Concepts, estimation and
  interpretation of SNP-based heritability*, Nat. Genet. 49 (2017), 1304–1310 (the GRM
  cross-product form).
