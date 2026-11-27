# Consistency of Haseman–Elston regression

For each $n \in \mathbb{N}$, let $\mu_n$ be a finite measure on a measurable space $\Omega_n$,
take an [LD-score model](../ld-score-regression/model.md) on $(\Omega_n, \mu_n)$ with $N_n$
individuals, $M_n$ markers and heritability $h^2$, the same for every $n$ (square-integrable
effects $\beta_k$ and noise terms $\varepsilon_i$ with
$\int \beta \beta^\top d\mu_n = (h^2/M_n)\, I$,
$\int \varepsilon \varepsilon^\top d\mu_n = (1 - h^2)\, I$ and
$\int \beta \varepsilon^\top d\mu_n = 0$), and a real $N_n \times M_n$ genotype matrix $X_n$ with
[genetic relationship matrix](grm.md) $A^{(n)}$. Suppose that, for a constant $C$ independent
of $n$:

- for every $n$, every cross-product $y_i y_j$ of
  [phenotypes](../ld-score-regression/pheno.md) with $i < j$ is square integrable;
- for every $n$ and every [pair](../../bioinformatics/sequence-alignment/multiple-sequence-alignment/pair-finset.md) $p$, the absolute row sum
  $\sum_q \bigl|\int d_p\, d_q \, d\mu_n\bigr|$ over the pairs $q$, where
  $d_{(i,j)} = y_i y_j - h^2 A^{(n)}_{ij}$ are the [deviations](he-dev.md), is at most $C$;
- $S_n = \sum_{i<j} \bigl(A^{(n)}_{ij}\bigr)^2 \to \infty$ as $n \to \infty$.

Then for every $t > 0$ the [Haseman–Elston estimator](he-estimate.md) $\hat h^2_n$ computed from
$A^{(n)}$ and the phenotypes satisfies

$$\mu_n\bigl(\{\omega : |\hat h^2_n(\omega) - h^2| \ge t\}\bigr) \to 0 \qquad (n \to \infty).$$

When every $\mu_n$ is a probability measure, $\hat h^2_n$ converges in probability to $h^2$, and
the row sums are those of the covariance matrices of the cross-products. The row-sum condition
is a weak-dependence condition on the pairs; it is a hypothesis of the theorem, not a
consequence of a distributional assumption on the phenotypes.
