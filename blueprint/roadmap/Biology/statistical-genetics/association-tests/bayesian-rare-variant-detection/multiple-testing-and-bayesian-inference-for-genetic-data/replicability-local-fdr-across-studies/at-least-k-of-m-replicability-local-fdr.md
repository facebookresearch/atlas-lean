# At-least-$k$-of-$m$ replicability local fdr

**Model.** Genes $i = 1, \dots, n$ are measured in $m > 1$ studies, giving z-scores $Z_{i,\cdot} = (Z_{i,1}, \dots, Z_{i,m})$. Each study $j$ follows Efron's two-groups model with null proportion $\pi_0^j$, null and non-null densities $f_0^j, f_1^j$, and mixture density $f^j = \pi_0^j f_0^j + (1 - \pi_0^j) f_1^j$. The unknown parameter of gene $i$ is a configuration $H_{i,\cdot} \in \{0,1\}^m$ ($H_{i,j} = 1$ for non-null in study $j$) with prior $\pi(h)$, and z-scores are conditionally independent given the configuration:

$$P(Z_{i,\cdot} \mid h) = \prod_{j=1}^m f_0^j(Z_{i,j})^{1 - h_j} f_1^j(Z_{i,j})^{h_j}.$$

A gene is called *replicated* if it is non-null in at least $k$ studies, $\mathcal H_1 = \{h : |h| \ge k\}$ with $|h| = \sum_j h_j$. Its replicability local false discovery rate is the posterior probability of the complement,

$$\mathrm{fdr}_k(Z_{i,\cdot}) = \sum_{h : |h| < k} \frac{P(Z_{i,\cdot} \mid h)\, \pi(h)}{\sum_{h'} P(Z_{i,\cdot} \mid h')\, \pi(h')}.$$

**Independent studies.** If the prior factorizes, $\pi(h) = \prod_j (\pi_0^j)^{1 - h_j} (1 - \pi_0^j)^{h_j}$, then

$$\mathrm{fdr}_k(Z_{i,\cdot}) = \sum_{h : |h| < k} \prod_{j=1}^m \frac{\bigl(\pi_0^j f_0^j(Z_{i,j})\bigr)^{1 - h_j} \bigl((1 - \pi_0^j) f_1^j(Z_{i,j})\bigr)^{h_j}}{f^j(Z_{i,j})},$$

the probability that a Poisson-binomial sum of the per-study posterior non-null indicators is below $k$. Dynamic programming over studies and running counts evaluates it in $O(mk)$ time per gene, $O(nmk)$ in total.

**Independent study clusters.** If studies fall into independent clusters $C_1, \dots, C_M$ with $\pi(h) = \prod_l P(h_{C_l})$, let $V_{C_l}[i, s]$ be the posterior probability that gene $i$ has exactly $s$ non-null studies within $C_l$ (computed from any within-cluster prior). Convolving these count distributions across clusters by dynamic programming gives the distribution of the total count, and $\mathrm{fdr}_k$ is its mass below $k$, in $O(k^2 M)$ time per gene.

## Depends on

- [Local false discovery rate](../../../../../../Probability/hypothesis-testing/two-groups-model-and-local-false-discovery-rates/local-fdr.md)
- [Distribution of a sum of independent Bernoulli variables](../../../../../../Probability/distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/bernoulli-sum-pmf.md)

## Expansion

Under a factorized prior the posterior of $h$ factorizes too, so the per-study posterior null probabilities $\pi_0^j f_0^j(Z_{i,j})/f^j(Z_{i,j})$ are independent Bernoulli parameters, and $\mathrm{fdr}_k$ is a lower tail of their sum. Adding one study at a time updates the count distribution by $U_j(s) = p_{0j} U_{j-1}(s) + p_{1j} U_{j-1}(s - 1)$, truncated at $s = k$. The cluster version replaces single studies by blocks whose internal count distribution is learned separately (by EM over the cluster's configurations), which keeps the exponential $2^m$ configuration space confined to small blocks. Thresholding $\mathrm{fdr}_k$ (or its running average over the selected genes) controls the Bayes FDR of declaring genes replicated, rather than merely significant in some study.

## Sources

- D. Amar, R. Shamir, D. Yekutieli, "Extracting replicable associations across multiple studies: empirical Bayes algorithms for controlling the false discovery rate", *PLOS Computational Biology* 13 (2017), e1005700, <https://doi.org/10.1371/journal.pcbi.1005700>; preprint "Extracting replicable associations across multiple studies: algorithms for controlling the false discovery rate", arXiv:1609.01118 (2016), Results: "Preliminaries and notations", "An $O(mnk)$ algorithm under independence assumption" (lemma and proposition) and "An algorithm for combining study clusters". <https://doi.org/10.48550/arXiv.1609.01118>
