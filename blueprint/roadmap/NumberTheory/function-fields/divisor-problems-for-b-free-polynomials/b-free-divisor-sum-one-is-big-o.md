# Asymptotic count of B-free polynomials

Let $F$ be a finite field with $q$ elements, write
$|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$ assign a natural number to each
polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$; let $\kappa_{\min}$
be the minimum of $\kappa(P)$ over the monic irreducible $P$. Let $\tilde D_{\kappa,1}(N)$ be the
sum of $d_1(f)$ (which is $1$ for monic $f$) over the monic $B_\kappa$-free $f$ of degree at most
$N$, where $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$ with $P$ monic irreducible divides it.
Then for every $\varepsilon > 0$,

$$
\tilde D_{\kappa,1}(N) - \frac{q^N}{1 - 1/q} \prod_P \bigl(1 - |P|^{-\kappa(P)}\bigr) =
O\bigl(q^{(1/\kappa_{\min} + \varepsilon) N}\bigr)
$$

as $N \to \infty$, the product running over the monic irreducible $P$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 1, first formula.
