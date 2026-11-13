# Asymptotic for the $B_\kappa$-free sum of the divisor function

Let $F$ be a finite field
with $q$ elements and let $\kappa$ assign to each polynomial in $F[T]$ a natural number, with
$\kappa(P) \ge 2$ for every monic irreducible $P$. A polynomial $f$ is $B_\kappa$-free when
$P^{\kappa(P)}$ does not divide $f$ for any monic irreducible $P$; $d_2(f)$ is the number of
ordered pairs of monic polynomials with product $f$; $\tilde D_{B_\kappa,2}(N)$ is the sum of
$d_2(f)$ over the $B_\kappa$-free monic $f$ of degree at most $N$; $\kappa_{\min}$ is the minimum
of $\kappa(P)$ over the monic irreducible $P$; and for a monic irreducible $P$ we write
$\kappa_P = \kappa(P)$ and $|P| = q^{\deg P}$ for its norm. Then for every $\varepsilon > 0$, as
$N \to \infty$,

$$
\tilde D_{B_\kappa,2}(N) = \frac{q^N}{1 - 1/q}
\prod_P \left( 1 - \frac{\kappa_P + 1}{|P|^{\kappa_P}} + \frac{\kappa_P}{|P|^{\kappa_P + 1}} \right)
\left( N + 1 - \frac{1}{q - 1} +
\sum_P \frac{\kappa_P (\kappa_P + 1) \deg(P) (|P| - 1)}{|P|^{\kappa_P + 1} - |P| (\kappa_P + 1) +
\kappa_P} \right) + O\left( q^{(1/\kappa_{\min} + \varepsilon) N} \right),
$$

where the product and the sum run over the monic irreducible polynomials $P$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 1, second formula.
