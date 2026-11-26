# Unbiased local SNP heritability from GWAS summary statistics

Let $y_i = x_i^\top \beta + \epsilon_i$ ($i = 1, \dots, n$), where $x_i \in \mathbb R^p$ are the standardized genotypes (mean $0$, variance $1$) of individual $i$ at the $p$ typed SNPs of a locus, $\beta \in \mathbb R^p$ is a fixed effect vector, $\epsilon_i \sim N(0, \sigma_e^2)$, and the trait is standardized, $\operatorname{Var}(y) = 1$. With $V = \operatorname{Cov}(x_i)$ the LD matrix, the **local SNP heritability** is

$$h^2_{g,\mathrm{local}} = \beta^\top V \beta, \qquad \sigma_e^2 = 1 - h^2_{g,\mathrm{local}} .$$

The GWAS marginal estimates $\hat\beta_{\mathrm{GWAS},j} = \tfrac1n X_j^\top y$ satisfy, by the central limit theorem,

$$\hat\beta_{\mathrm{GWAS}} \approx N\!\Bigl(V\beta,\ \frac{1 - h^2_{g,\mathrm{local}}}{n}\, V\Bigr).$$

**Proposition.** If $V$ is invertible, then $E[\hat\beta_{\mathrm{GWAS}}^\top V^{-1}\hat\beta_{\mathrm{GWAS}}] = p(1 - h^2_{g,\mathrm{local}})/n + h^2_{g,\mathrm{local}}$, so

$$\hat h^2_{g,\mathrm{local}} = \frac{n\,\hat\beta_{\mathrm{GWAS}}^\top V^{-1}\hat\beta_{\mathrm{GWAS}} - p}{n - p}$$

is unbiased, with variance (under the normal approximation)

$$\operatorname{Var}\bigl[\hat h^2_{g,\mathrm{local}}\bigr] = \Bigl(\frac{n}{n - p}\Bigr)^2 \Bigl(\frac{2p(1 - h^2_{g,\mathrm{local}})}{n} + 4h^2_{g,\mathrm{local}}\Bigr)\frac{1 - h^2_{g,\mathrm{local}}}{n},$$

which tends to $2p/(n - p)^2$ as $h^2_{g,\mathrm{local}} \to 0$. If $V$ has rank $q < p$ (SNPs in perfect LD), replacing $V^{-1}$ by the Moore–Penrose pseudoinverse $V^\dagger$ and $p$ by $q$ gives the unbiased estimator $(n\hat\beta_{\mathrm{GWAS}}^\top V^\dagger\hat\beta_{\mathrm{GWAS}} - q)/(n - q)$, because $\operatorname{tr}(V^\dagger V) = q$.

## Proof sketch

The naive plug-in $\hat\beta^\top V^{-1}\hat\beta$ estimates $\beta^\top V V^{-1} V\beta = \beta^\top V\beta$ but carries the noise term $\operatorname{tr}(V^{-1}\operatorname{Cov}\hat\beta) = p(1 - h^2)/n$. Setting $\hat\beta^\top V^{-1}\hat\beta = (1 - \hat h^2)p/n + \hat h^2$ and solving gives the estimator; its expectation is then $h^2$. The variance is the variance of a noncentral quadratic form in a Gaussian vector, rescaled by $n/(n-p)$. For loci with little signal ($h^2_{g,\mathrm{local}} \ll p/n$) the variance is dominated by $2p/(n-p)^2$, so the estimator is useful only when $n \gg p$. Writing $V = \sum_i w_i u_i u_i^\top$, the quadratic form is $\sum_i (u_i^\top\hat\beta)^2/w_i$, a weighted sum of squared projections of the GWAS effects onto the LD eigenvectors.

## Sources

- H. Shi, G. Kichaev and B. Pasaniuc, "Contrasting the genetic architecture of 30 complex traits from summary association data", American Journal of Human Genetics 99 (2016), 139–153, Material and Methods, Equations (1)–(6) and "Accounting for Rank Deficiencies in LD", <https://doi.org/10.1016/j.ajhg.2016.05.013> (PMCID: PMC5005444).
