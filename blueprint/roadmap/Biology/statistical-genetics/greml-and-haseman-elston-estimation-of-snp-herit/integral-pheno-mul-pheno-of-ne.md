# Haseman–Elston identity for distinct individuals

Take an [LD-score model](../ld-score-regression/model.md) with heritability $h^2$ on a measure
space $(\Omega, \mu)$: square-integrable effects $\beta_k$ and noise terms $\varepsilon_i$ with
$\int \beta \beta^\top d\mu = (h^2/M)\, I$, $\int \varepsilon \varepsilon^\top d\mu = (1 - h^2)\, I$
and $\int \beta \varepsilon^\top d\mu = 0$. Then for every real $N \times M$ genotype matrix $X$,
the [phenotypes](../ld-score-regression/pheno.md) of two distinct individuals $i \ne j$ satisfy

$$\int y_i\, y_j \, d\mu = h^2 A_{ij},$$

where $A = XX^\top/M$ is the [genetic relationship matrix](grm.md). The cross-product moments
are linear in the relationship entries, with slope the SNP heritability; this is the identity
behind [Haseman–Elston regression](he-estimate.md). The measure need not be a probability
measure; for a probability measure the left side is the expected cross-product, which is the
covariance of $y_i$ and $y_j$ when the effects and noise have mean zero.
