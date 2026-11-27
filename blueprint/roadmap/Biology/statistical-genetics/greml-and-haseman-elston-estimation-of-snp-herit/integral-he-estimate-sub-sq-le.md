# Integrated squared-error bound for Haseman–Elston regression

Let $\mu$ be a finite measure on $\Omega$. Take an
[LD-score model](../ld-score-regression/model.md) with heritability $h^2$ on $(\Omega, \mu)$
(square-integrable effects $\beta_k$ and noise terms $\varepsilon_i$ with
$\int \beta \beta^\top d\mu = (h^2/M)\, I$, $\int \varepsilon \varepsilon^\top d\mu = (1 - h^2)\, I$
and $\int \beta \varepsilon^\top d\mu = 0$) and a real $N \times M$ genotype matrix $X$ whose
[genetic relationship matrix](grm.md) $A$ is not diagonal: $S = \sum_{i<j} A_{ij}^2 \ne 0$.
Suppose that

- every cross-product $y_i y_j$ of [phenotypes](../ld-score-regression/pheno.md) with $i < j$
  is square integrable, and
- for a constant $C$, every absolute row sum of the matrix $K_{pq} = \int d_p\, d_q \, d\mu$ of
  the [deviations](he-dev.md) $d_{(i,j)} = y_i y_j - h^2 A_{ij}$, indexed by the
  [pairs](../../bioinformatics/sequence-alignment/multiple-sequence-alignment/pair-finset.md) $p$ and $q$, is at most $C$: $\sum_q |K_{pq}| \le C$ for every pair $p$.

Then the [Haseman–Elston estimator](he-estimate.md) $\hat h^2$ computed from $A$ and the
phenotypes satisfies

$$\int \bigl(\hat h^2 - h^2\bigr)^2 \, d\mu \le \frac{C}{S}.$$

When $\mu$ is a probability measure, $K$ is the covariance matrix of the cross-products
$y_i y_j$, $i < j$, and the left side is the mean-squared error of $\hat h^2$.
