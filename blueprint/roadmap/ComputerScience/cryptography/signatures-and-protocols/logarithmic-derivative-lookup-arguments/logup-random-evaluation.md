# Soundness of checking the logarithmic-derivative identity at a random point

Under the hypotheses of the logarithmic-derivative lemma, suppose the rational identity fails for given $\mathbf{f},\mathbf{t},\mathbf{m}$. Then for $\alpha$ uniform in $\mathbb{F}\setminus\{f_1,\dots,f_n,t_1,\dots,t_T\}$,

$$
\Pr\Bigl[\sum_i\frac{1}{\alpha-f_i}=\sum_j\frac{m_j}{\alpha-t_j}\Bigr]\le\frac{n+T-1}{|\mathbb{F}|-n-T}.
$$

Hence a lookup argument may commit to $\mathbf{m}$, receive $\alpha$, and prove the scalar identity via helper columns $h_i=1/(\alpha-f_i)$ and $g_j=m_j/(\alpha-t_j)$, each defined by a degree-$2$ constraint.

## Proof sketch

Multiply both sides by $\prod_i(X-f_i)\prod_j(X-t_j)$: the identity becomes equality of two polynomials of degree at most $n+T-1$, which differ by assumption and therefore agree on at most $n+T-1$ points. Excluding the at most $n+T$ poles gives the denominator.

## Depends on

- [Logarithmic-derivative characterization of set inclusion](logup-lemma.md)

## Proof depends on

- [Logarithmic-derivative characterization of set inclusion](logup-lemma.md)

## Sources

- Ulrich Haböck, "Multivariate Lookups Based on Logarithmic Derivatives", IACR ePrint 2022/1530 (2022).
