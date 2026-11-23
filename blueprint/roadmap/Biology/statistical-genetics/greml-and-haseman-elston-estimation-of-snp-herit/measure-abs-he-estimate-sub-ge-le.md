# Chebyshev bound for Haseman–Elston regression

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

Then for every $t > 0$ the [Haseman–Elston estimator](he-estimate.md) $\hat h^2$ computed from
$A$ and the phenotypes satisfies

$$\mu\bigl(\{\omega : |\hat h^2(\omega) - h^2| \ge t\}\bigr) \le \frac{C}{t^2 S}.$$

It follows from the [mean-squared error bound](integral-he-estimate-sub-sq-le.md) by Chebyshev's
inequality. For a probability measure it bounds the probability that the estimate misses $h^2$
by at least $t$.
