# Divisor-count bound over $\kappa$-th powers of monic polynomials

Let $F$ be a finite
field with $q$ elements and let $\kappa$ assign a natural number to each polynomial in $F[T]$,
with $\kappa(P) \ge 2$ for every monic irreducible $P$. For monic $r = \prod_P P^{\nu_P}$ write
$r^\kappa = \prod_P P^{\nu_P \kappa(P)}$, and let $\kappa_{\min}$ be the minimum of $\kappa(P)$
over the monic irreducible $P$. Then for every $\varepsilon > 0$, as $N \to \infty$,

$$\sum_{r \text{ monic},\ \deg r^\kappa \le N} \ \sum_{f \mid r^\kappa} \ \sum_{\ell \mid f} 1 =
O\left(q^{(1/\kappa_{\min} + \varepsilon) N}\right),$$

where $f$ runs over the monic divisors of $r^\kappa$ and $\ell$ over the monic divisors of $f$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (7).
