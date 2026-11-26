# Truncated-SVD and multi-locus local heritability estimators

In the setting of [the single-locus estimator](unbiased-local-snp-heritability-from-gwas-summary-statistics.md), suppose the in-sample LD matrix is replaced by a reference-panel estimate $\hat V$ with eigenpairs $(\hat w_i, \hat u_i)$, $\hat w_1 \ge \hat w_2 \ge \cdots$. For $k$ less than the rank of $\hat V$ define the truncated quadratic form

$$g(\hat\beta, k) = \sum_{i=1}^{k} \frac{(\hat u_i^\top \hat\beta)^2}{\hat w_i} .$$

**Single locus.** Suppose $\hat\beta \sim N(V\beta, V(1 - h^2_{g,\mathrm{local}})/n)$ and the $k$ leading eigenvectors of $\hat V$ are eigenvectors of $V$, $V\hat u_i = w_i\hat u_i$ for $i \le k$. Then each retained term has the exact expectation

$$E\!\left[\frac{(\hat u_i^\top\hat\beta)^2}{\hat w_i}\right] = \frac{(1 - h^2_{g,\mathrm{local}})\, w_i/n + w_i^2 (\hat u_i^\top\beta)^2}{\hat w_i}, \qquad i \le k,$$

so matching eigenvectors alone does not give a noise term of $1/n$ per direction: with zero signal the contribution is $w_i/(n\hat w_i)$. For example, the $2\times 2$ correlation matrices with off-diagonal entries $\tfrac12$ ($V$) and $\tfrac14$ ($\hat V$) share their top eigenvector, but $w_1/\hat w_1 = 1.5/1.25 = 1.2$. If in addition the retained eigenvalues match, $\hat w_i = w_i$ for $i \le k$, then

$$E[g(\hat\beta, k)] = \frac{k(1 - h^2_{g,\mathrm{local}})}{n} + \sum_{i=1}^{k} w_i (\hat u_i^\top\beta)^2,$$

and since $h^2_{g,\mathrm{local}} = \sum_i w_i (u_i^\top\beta)^2$ is dominated by its leading terms, this motivates the bias-corrected truncated estimator

$$\tilde h^2_{g,\mathrm{local}} = \frac{n\, g(\hat\beta, k) - k}{n - k}.$$

With a reference-panel $\hat V$ whose eigenpairs only approximate those of $V$, the expectation display and the estimator's correction are approximations, which is how Shi et al. use them (their Equations 7–8).

**Many independent loci.** If the genome splits into $m$ independent loci, $y = \sum_{i=1}^m X_i\beta_i + \epsilon$, then $\operatorname{Var}(y) = \sum_i h^2_{g,\mathrm{local},i} + \sigma_e^2$ with $\sigma_e^2 = 1 - \sum_j h^2_{g,\mathrm{local},j}$, and the local estimates solve the linear system

$$\hat h^2_{g,\mathrm{local},i} = \frac{n\, g(\hat\beta_i, k_i) - \bigl(1 - \sum_{j \ne i}\hat h^2_{g,\mathrm{local},j}\bigr) k_i}{n - k_i}, \qquad i = 1, \dots, m .$$

With a common truncation $k_i = k$, summing gives the genome-wide SNP heritability estimate

$$\hat h^2_g = \frac{n}{n - mk}\sum_{i=1}^m g(\hat\beta_i, k) - \frac{mk}{n - mk}, \qquad \operatorname{Var}[\hat h^2_g] \approx \Bigl(\frac{n}{n - mk}\Bigr)^2 \frac{2mk}{(n - k)^2},$$

which is unstable unless $n/(n - mk)$ is small (the authors recommend $< 2$). If instead the genome-wide $h_g^2$ is known, the local estimates decouple:

$$\hat h^2_{g,\mathrm{local},i} = g(\hat\beta_i, k) - \frac{k}{n}(1 - h_g^2), \qquad \operatorname{Var}[\hat h^2_{g,\mathrm{local},i}] = \operatorname{Var}[g(\hat\beta_i, k)] + \Bigl(\frac{k}{n}\Bigr)^2\operatorname{Var}[h_g^2] .$$

## Remarks

Noise in $\hat V$ mostly corrupts its small eigenvalues, whose reciprocals blow up in the full quadratic form, while the leading projections carry most of the signal. Truncation keeps only $k$ terms, each contributing $(1 - h^2)/n$ of pure noise in expectation when the retained eigenpairs match, which the $-k$ and $n - k$ correct; a mismatch $\hat w_i \ne w_i$ rescales both the noise and the signal of term $i$ by $w_i/\hat w_i$. Ridge regularization ($\hat w_i \mapsto \hat w_i + \lambda$) instead shrinks every term and biases the estimate downwards. With several loci the residual variance depends on all local heritabilities, which couples the corrections into an $m \times m$ linear system; summing the equations with equal $k$ gives the closed form for $\hat h_g^2$.

## Depends on

- [Unbiased local SNP heritability from GWAS summary statistics](unbiased-local-snp-heritability-from-gwas-summary-statistics.md)

## Sources

- H. Shi, G. Kichaev and B. Pasaniuc, "Contrasting the genetic architecture of 30 complex traits from summary association data", American Journal of Human Genetics 99 (2016), 139–153, Material and Methods, Equations (7)–(15), <https://doi.org/10.1016/j.ajhg.2016.05.013> (PMCID: PMC5005444).
