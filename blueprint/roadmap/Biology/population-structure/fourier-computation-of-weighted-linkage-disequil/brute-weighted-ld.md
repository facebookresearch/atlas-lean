# Brute-force weighted linkage disequilibrium sum

Let $S$ be a finite set of SNPs with grid cells $c : S \to \mathbb{N}$, genotypes $g_i(x)$ of $m$ individuals and weights $w : S \to \mathbb{R}$. The brute-force weighted LD sum at cell offset $j$ is

$$\mathrm{WLD}_j = \sum_{x, y \in S,\ c(y) = c(x) + j} \hat z(x, y)\, w(x)\, w(y),$$

where $\hat z$ is the [sample covariance](sample-cov.md).
