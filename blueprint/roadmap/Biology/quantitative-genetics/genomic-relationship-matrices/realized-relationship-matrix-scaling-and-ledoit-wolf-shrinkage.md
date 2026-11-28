# Realized relationship matrix scaling and Ledoit–Wolf shrinkage

**Setting.** For $n$ lines and $m$ biallelic markers let $X_{ik} \in \{0,1,2\}$ be allele counts, $p_k$ the allele frequency of marker $k$, $q_k = 1 - p_k$, and $W$ the centered genotype matrix, $W_{ik} = X_{ik} - 2p_k$. Under the infinitesimal model $a = \tilde W u$ (sum over causal loci with i.i.d. effects $u_k$), the additive relationship matrix $A$ satisfies $G = \operatorname{var}(a) = \sigma^2 A$ with mean diagonal $\langle A_{ii}\rangle = 1 + f$, where $f$ is the inbreeding coefficient of the current population.

**Scaled estimator.** Requiring $\langle A_{ii}\rangle = 1+f$ fixes the scale:

$$\hat A = \frac{WW^\top}{2\sum_k p_kq_k},$$

and in terms of the $n\times n$ covariance matrix $\Sigma = \operatorname{var}[w]$ of a randomly sampled locus, $A = (\Sigma + \mathbb{E}[w]\mathbb{E}[w]^\top)/(2\mathbb{E}[pq])$, which $\hat A$ estimates with the sample covariance $S = m^{-1}WW^\top - \langle W_{\bullet k}\rangle\langle W_{\bullet k}\rangle^\top$.

**Shrinkage estimator.** When $m$ is not large relative to $n$, replace $S$ by $\hat\Sigma = \delta\langle S_{ii}\rangle I + (1-\delta)S$, $\delta \in [0,1]$:

$$\hat A^* = \frac{\delta\langle S_{ii}\rangle I + (1-\delta)S + \langle W_{\bullet k}\rangle\langle W_{\bullet k}\rangle^\top}{2\langle p_jq_j\rangle}.$$

The intensity minimizing $\mathbb{E}\|\hat\Sigma - \Sigma\|_F^2$ is estimated (Ledoit–Wolf) from the columns $Z_{\bullet k}$ of the row-centered marker matrix, $S = m^{-1}ZZ^\top$, as

$$\delta = \frac{m^{-2}\sum_{k=1}^{m}\big\|Z_{\bullet k}Z_{\bullet k}^\top - S\big\|_F^2}{\big\|S - \langle S_{ii}\rangle I\big\|_F^2},$$

truncated to $[0,1]$. Shrinkage is negligible when $n/m \ll \mathrm{CV}^2$, the squared coefficient of variation of the eigenvalues of $S$.

## Remarks

Writing $\operatorname{tr}G = \sigma^2 n(1+f)$ and expanding $\operatorname{tr}(\tilde W\tilde W^\top)$ locus by locus with per-locus inbreeding $f_k$ gives $\sigma^2 = 2\sigma_u^2\langle p_kq_k\rangle$ and $f = \sum_k\beta_kf_k$ with weights $\beta_k \propto p_kq_k$, which yields the denominator $2\sum_k p_kq_k$; the result needs no identity-by-descent argument and holds for inbred lines, consistent with an identity-by-state view of genetic covariance. The target $\langle S_{ii}\rangle I$ keeps the trace, so $\mathbb{E}\operatorname{tr}\hat\Sigma = \operatorname{tr}\Sigma$, and the mean-vector term is left unshrunk, so the inbreeding level is preserved. The numerator of $\delta$ estimates the sampling variance of $S$ and the denominator the distance of $S$ from the target; with few markers (for example a few hundred) relative to lines, the shrunk matrix improved the accuracy of genomic breeding-value prediction by BLUP in the source.

## Sources

- J. B. Endelman and J.-L. Jannink, "Shrinkage estimation of the realized relationship matrix", G3: Genes, Genomes, Genetics 2 (2012), 1405, Equations (3)–(20), <https://doi.org/10.1534/g3.112.004259>, PMCID PMC3484671.
- O. Ledoit and M. Wolf, "A well-conditioned estimator for large-dimensional covariance matrices", Journal of Multivariate Analysis 88 (2004), 365–411, <https://doi.org/10.1016/S0047-259X(03)00096-4>.
