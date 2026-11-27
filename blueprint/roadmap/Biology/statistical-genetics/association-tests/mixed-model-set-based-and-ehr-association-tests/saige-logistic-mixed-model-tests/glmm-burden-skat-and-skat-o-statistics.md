# Burden, SKAT and SKAT-O statistics under a generalized linear mixed model

Fit the null generalized linear mixed model with relationship matrix $\Psi$ as in the [variance-ratio adjusted score test](variance-ratio-adjusted-score-test.md) (identity link with Gaussian error for continuous traits, logistic link for binary traits), giving $\hat\mu$, working weights $\hat W$ and projection $\hat P$. For a region with $q$ variants and genotype matrix $G = (G_1, \dots, G_q)$, let $S_j = G_j^\top (Y - \hat\mu)$ be the single-variant scores, $\tilde G = G - X (X^\top \hat W X)^{-1} X^\top \hat W G$ the covariate-adjusted genotypes, and $D_w = \operatorname{diag}(w_1, \dots, w_q)$ variant weights (default $w_j$ is the Beta$(1, 25)$ density at the minor allele frequency). Then, under $H_0$ of no genetic effect in the region,

$$Q_{\mathrm{Burden}} = \Bigl(\sum_{j=1}^{q} w_j S_j\Bigr)^2 \sim \lambda_B\, \chi^2_1, \qquad \lambda_B = \mathbf{1}^\top D_w \tilde G^\top \hat P \tilde G D_w \mathbf{1},$$

$$Q_{\mathrm{SKAT}} = \sum_{j=1}^{q} w_j^2 S_j^2 \sim \sum_{j=1}^{q} \lambda_j\, \chi^2_{1,j},$$

where the $\chi^2_{1,j}$ are independent and $\lambda_j$ are the eigenvalues of $D_w \tilde G^\top \hat P \tilde G D_w$. SKAT-O uses $Q_\rho = (1 - \rho) Q_{\mathrm{SKAT}} + \rho Q_{\mathrm{Burden}}$, $0 \le \rho \le 1$, over the grid $\rho \in \{0, 0.1^2, 0.2^2, 0.3^2, 0.4^2, 0.5^2, 0.5, 1\}$, with the minimum $p$-value calibrated by numerical integration.

To avoid one linear solve per variant, SAIGE-GENE approximates $\tilde G^\top \hat P \tilde G \approx \hat R^{1/2} \tilde G^\top \hat P_s \tilde G \hat R^{1/2}$, where $\hat P_s$ is the projection built from a sparse relationship matrix that keeps only close relatives and $\hat R$ is diagonal with entries $\hat r_s = \tilde g^\top \hat P \tilde g / \tilde g^\top \hat P_s \tilde g$, estimated separately for minor allele count categories $1, 2, 3, 4, 5, 6$–$10$, $11$–$20$ and $> 20$.

## Depends on

- [Variance-ratio adjusted score test in a logistic mixed model](variance-ratio-adjusted-score-test.md)
- [SKAT variance-component score statistic](../../skat-variance-component-test/skat-q.md)
- [Mixture matrix of the SKAT statistic](../../skat-variance-component-test/skat-mixture-matrix.md)

## Expansion

The score vector $S = (S_1, \dots, S_q)$ is asymptotically $N(0, \tilde G^\top \hat P \tilde G)$ under the null; the burden statistic is the square of one linear combination of it and the SKAT statistic a quadratic form, which gives the scaled $\chi^2_1$ and weighted chi-square laws. Including close relatives in the denominator of the variance ratio reduces its variability for very rare variants. For binary traits the variances are further calibrated by single-variant saddlepoint or efficient-resampling $p$-values.

## Sources

- W. Zhou et al., *Scalable generalized linear mixed model for region-based association tests in large biobanks and cohorts*, Nat. Genet. 52 (2020), 634–639. <https://doi.org/10.1038/s41588-020-0621-6> (PMCID: PMC7871731) Online Methods, "Gene-based association tests (Step 2)" and "Approximate $\tilde G^\top \hat P \tilde G$".
