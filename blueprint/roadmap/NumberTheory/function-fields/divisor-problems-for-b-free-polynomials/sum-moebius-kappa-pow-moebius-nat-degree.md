# Euler-product asymptotic for a degree-weighted Möbius sum over $\kappa$-th powers

Let
$F$ be a finite field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let
$\mu$ be the Möbius function of $F[T]$. Let $\kappa$ assign a natural number to each polynomial in
$F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$. For monic $r = \prod_P P^{\nu_P}$
write $r^\kappa = \prod_P P^{\nu_P \kappa(P)}$, and let $\kappa_{\min}$ be the minimum of
$\kappa(P)$ over the monic irreducible $P$. Let $m \in F[T]$ be monic. Then for every
$\varepsilon > 0$, as $N \to \infty$,

$$\sum_{\substack{r \text{ monic},\ \deg r^\kappa \le N \\ \gcd(r, m) = 1}}
\frac{\mu(r)}{|r^\kappa|} \sum_{f \mid r^\kappa} \sum_{g \mid f} \frac{\mu(g) \deg g}{|g|} =
\prod_{P \nmid m} \left(1 - \frac{\kappa(P) + 1}{|P|^{\kappa(P)}} +
\frac{\kappa(P)}{|P|^{\kappa(P) + 1}}\right)
\sum_{P \nmid m} \frac{\kappa(P) \deg P}{|P|^{\kappa(P) + 1} - |P| (\kappa(P) + 1) + \kappa(P)} +
O\left(q^{(1/\kappa_{\min} + \varepsilon - 1)(N + 1)}\right),$$

where $f$ runs over the monic divisors of $r^\kappa$, $g$ over the monic divisors of $f$, and $P$
in the product and in the sum over the monic irreducible polynomials not dividing $m$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 2.
