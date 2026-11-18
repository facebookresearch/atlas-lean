# Asymptotic count of B-free polynomials in an arithmetic progression

Let $F$ be a finite
field with $q$ elements, write $|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$
assign a natural number to each polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic
irreducible $P$; let $\kappa_{\min}$ be the minimum of $\kappa(P)$ over the monic irreducible $P$.
Let $m \ne 0$ and $a$ be polynomials in $F[T]$ with $a$ coprime to $m$, and let
$\tilde D_{\kappa,1}(N, a, m)$ be the sum of $d_1(f)$ (which is $1$ for monic $f$) over the monic
$B_\kappa$-free $f$ of degree at most $N$ with $f \equiv a \pmod m$, where $f$ is $B_\kappa$-free
when no $P^{\kappa(P)}$ with $P$ monic irreducible divides it. Then for every $\varepsilon > 0$,

$$
\tilde D_{\kappa,1}(N, a, m) -
\frac{q^N}{(1 - 1/q) \, |m|} \prod_{P \nmid m} \bigl(1 - |P|^{-\kappa(P)}\bigr) =
O\bigl(q^{(1/\kappa_{\min} + \varepsilon) N}\bigr)
$$

as $N \to \infty$, the product running over the monic irreducible $P$ not dividing $m$.

The paper's statement does not list the hypothesis $m \ne 0$; it is implicit, since $m$ is the
modulus of a progression.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 3, first formula.
