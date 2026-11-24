# Pooled-frequency GRM bias for independent individuals

Take **distinct, independent** individuals with allele counts $X_i,X_j$
and means $2p_1,2p_2$, where $p_1,p_2\in[0,1]$.
Use the fixed, equal-mixture reference frequency
$\bar p=(p_1+p_2)/2\in(0,1)$, not a frequency estimated from this same
pair. For the single-locus [GRM formula](../../quantitative-genetics/genomic-relationship-matrices/grm.md),

$$\mathbb E\frac{(X_i-2\bar p)(X_j-2\bar p)}{2\bar p(1-\bar p)}
=-\frac{(p_1-p_2)^2}{2\bar p(1-\bar p)}.$$

For two independent individuals both from the first population, still
using this same fixed reference frequency, the expectation is
$+(p_1-p_2)^2/(2\bar p(1-\bar p))$; the second population has the same
within-population expectation. Both biases vanish when $p_1=p_2$ and
have strict indicated signs when $p_1\ne p_2$.
They are proportional to the single-locus squared frequency difference,
the point-mass-locus specialization of [f2](f2.md).

## Depends on

- [Single-locus GRM expression](../../quantitative-genetics/genomic-relationship-matrices/grm.md)
- [f2](f2.md)

## Background

- [Unbiasedness under a common-frequency IBD model](../../quantitative-genetics/genomic-relationship-matrices/integral-grm.md)

## Expansion

Independence factors the centered-product expectation into
$(2p_i-2\bar p)(2p_j-2\bar p)$; substitution gives both formulas.
No Hardy–Weinberg assumption about each individual's count is needed
beyond its mean. Absence of a recorded IBD relationship alone is not a
mathematical independence hypothesis. The common-frequency unbiasedness
theorem is a contrasting special model, not a proof of this two-frequency
claim. Unequal mixture weights or an estimated reference frequency change
the expression; this page makes neither extension implicitly.

## Sources

- A. Manichaikul, J. C. Mychaleckyj, S. S. Rich, K. Daly, M. Sale and W.-M. Chen, "Robust relationship inference in genome-wide association studies", Bioinformatics 26 (2010), 2867–2873, <https://doi.org/10.1093/bioinformatics/btq559>. The expectation is derived above.
