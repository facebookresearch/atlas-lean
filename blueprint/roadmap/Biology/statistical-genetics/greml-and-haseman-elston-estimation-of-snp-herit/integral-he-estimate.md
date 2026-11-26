# Haseman–Elston estimate integrates to $h^2$ if the GRM is not diagonal

Take an [LD-score model](../ld-score-regression/model.md) with heritability $h^2$ on a measure
space $(\Omega, \mu)$: square-integrable effects $\beta_k$ and noise terms $\varepsilon_i$ with
$\int \beta \beta^\top d\mu = (h^2/M)\, I$, $\int \varepsilon \varepsilon^\top d\mu = (1 - h^2)\, I$
and $\int \beta \varepsilon^\top d\mu = 0$. Let $X$ be a real $N \times M$ genotype matrix whose
[genetic relationship matrix](grm.md) $A$ is not diagonal, that is,
$\sum_{i<j} A_{ij}^2 \ne 0$ ($A$ is symmetric). Let $\hat h^2(\omega)$ be the
[Haseman–Elston estimator](he-estimate.md) computed from $A$ and the
[phenotypes](../ld-score-regression/pheno.md) $y_1(\omega), \dots, y_N(\omega)$. Then

$$\int \hat h^2 \, d\mu = h^2.$$

The measure need not be a probability measure; when it is, $\hat h^2$ is an unbiased estimator
of the SNP heritability. For a diagonal $A$ (for instance when $N \le 1$) the estimator is
identically $0$ by the convention $x/0 = 0$.
