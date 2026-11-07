# Bound on the Möbius sum over κ-th powers

Let $F$ be a finite field with $q$ elements and
let $\kappa$ assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for
every monic irreducible $P$. Let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic
irreducible $P$, and for monic $r = \prod_P P^{\nu_P}$ write
$r^\kappa = \prod_P P^{\nu_P \kappa(P)}$. Then for every natural number $N \ge 1$,

$$
\Bigl|\sum_{r} \mu(r) \sum_{f \mid r^\kappa} \sum_{\ell \mid f} \mu(\ell)\Bigr| \le
q^{N/\kappa_{\min}},
$$

where $r$ runs over the monic polynomials with $\deg r^\kappa \le N$, $f$ and $\ell$ run over monic
divisors, $\mu$ is the Möbius function, and the exponent $N/\kappa_{\min}$ is a real number.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (6) (`integers-2026-A80-lem-8`).
