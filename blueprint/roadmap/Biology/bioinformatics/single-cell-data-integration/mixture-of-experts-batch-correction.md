# Mixture-of-experts batch correction

**Model.** Cells $i = 1,\dots,N$ have embeddings $Z_i \in \mathbb R^d$, batch indicators $\phi_i \in \{0,1\}^B$, and soft cluster assignments $R_{ki} \ge 0$ with $\sum_k R_{ki} = 1$. Let $\phi_i^* = (1, \phi_i^\top)^\top$ add an intercept and $\Phi^* = [\phi_1^*,\dots,\phi_N^*]$. Conditional on cluster (expert) $k$,

$$Z_i \mid \{\phi_i^*, \text{cluster } k\} \sim N\bigl(W_k^\top\phi_i^*,\ \sigma_k^2 I\bigr),$$

with a $(B+1) \times d$ coefficient matrix $W_k$ whose first row is a batch-independent intercept and whose remaining rows are batch effects.

**Estimation.** Each expert is fitted by weighted ridge regression with weights $R_{k\cdot}$:

$$W_k = \bigl(\Phi^*\operatorname{diag}(R_{k\cdot})\Phi^{*\top} + \Lambda\bigr)^{-1}\Phi^*\operatorname{diag}(R_{k\cdot})\,Z^\top, \qquad \Lambda = \operatorname{diag}(0, \lambda, \dots, \lambda),\ \lambda > 0.$$

The penalty is needed because the one-hot batch columns sum to the intercept, so $\Phi^*\operatorname{diag}(R_{k\cdot})\Phi^{*\top}$ is singular; leaving the intercept unpenalized shrinks only the batch terms toward zero.

**Correction.** Averaging over clusters, $Z_i = \sum_k R_{ki}\bigl[W_{k[0,\cdot]} + W_{k[1:B,\cdot]}^\top\phi_i\bigr] + \epsilon_i$, and the corrected embedding removes only the batch-dependent part:

$$\hat Z_i = Z_i - \sum_k R_{ki}\,W_{k[1:B,\cdot]}^\top\phi_i.$$

Alternating this correction with maximum-diversity soft clustering on $\hat Z$ until assignments stabilize gives the integrated embedding.

## Depends on

- [Maximum-diversity soft clustering](maximum-diversity-soft-clustering.md)

## Expansion

Within expert $k$ the Gaussian log-likelihood weighted by membership is $-\sum_i R_{ki}\|Z_i - W_k^\top\phi_i^*\|^2/(2\sigma_k^2)$ plus constants; adding the penalty $\sum_{b \ge 1}\lambda\|W_{k[b,\cdot]}\|^2$ and solving the normal equations gives the ridge solution above. Fitting a separate linear batch effect per cluster lets the correction vary with cell type, so a batch shift that differs between cell types is not forced to a single global value, while keeping the intercepts preserves between-cluster (cell-type) differences. Setting $\phi_i^* = (1,0,\dots,0)^\top$ for every cell of a reference dataset leaves those cells unchanged ($\hat Z_i = Z_i$) and maps query datasets onto the reference.

## Sources

- I. Korsunsky, N. Millard, J. Fan et al., "Fast, sensitive and accurate integration of single-cell data with Harmony", Nature Methods 16 (2019) 1289–1296, Supplementary Note 1, Section 3 ("Linear Mixture Model Correction", Eqs (9)–(14), Algorithm 3), <https://doi.org/10.1038/s41592-019-0619-0> (PMC6884693).
