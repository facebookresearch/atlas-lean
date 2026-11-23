# Deviation of a phenotype cross-product from $h^2 A_{ij}$

In an [LD-score model](../ld-score-regression/model.md) with heritability $h^2$ on a measure
space $(\Omega, \mu)$, and for a real $N \times M$ genotype matrix $X$ with
[genetic relationship matrix](grm.md) $A$, the deviation of a pair $p = (i, j)$ of individuals
is the function

$$d_p = y_i\, y_j - h^2 A_{ij}$$

on $\Omega$, where $y$ is the [phenotype](../ld-score-regression/pheno.md). It is defined for
every pair, including $i = j$. For $i \ne j$,
$h^2 A_{ij} = \int y_i y_j \, d\mu$ by the
[Haseman–Elston identity](integral-pheno-mul-pheno-of-ne.md), so for a probability measure
$d_p$ is the cross-product minus its mean; for $i = j$ the integral of $y_i^2$ is
$h^2 A_{ii} + 1 - h^2$ instead. When $\mu$ is a probability measure, $p = (i, j)$ and
$q = (k, l)$ with $i \ne j$ and $k \ne l$, and the cross-products $y_i y_j$ and $y_k y_l$ are
square integrable, $\int d_p\, d_q \, d\mu$ is the covariance of these two cross-products.
