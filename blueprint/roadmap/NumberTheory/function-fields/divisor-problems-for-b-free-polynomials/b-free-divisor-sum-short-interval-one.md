# B-free polynomials in short intervals

Let $F$ be a finite field with $q$ elements, write
$|f| = q^{\deg f}$ for nonzero $f \in F[T]$, and let $\kappa$ assign a natural number to each
polynomial in $F[T]$, with $\kappa(P) \ge 2$ for every monic irreducible $P$; let $\kappa_{\min}$
be the minimum of $\kappa(P)$ over the monic irreducible $P$. Assume $\kappa$ is symmetric:
$\kappa(P^*) = \kappa(P)$ for every monic irreducible $P$ with $P(0) \ne 0$, where $P^*$ is the
monic scalar multiple of the reversed polynomial $T^{\deg P} P(1/T)$. Let
$c > (1 + 2/\kappa_{\min})/3$ and $\varepsilon > 0$. Then there is a constant $C$ such that for
all sufficiently large $N$, every monic $A \in F[T]$ of degree $N$ and every natural number
$\Delta$ with $cN \le \Delta \le N - 2$,

$$
\Bigl|\sum_f d_1(f) - q^{\Delta + 1} \prod_P \bigl(1 - |P|^{-\kappa(P)}\bigr)\Bigr| \le
C q^{(N - \Delta)/2 + (1/\kappa_{\min} + \varepsilon) N},
$$

where $f$ runs over the $B_\kappa$-free $f \in F[T]$ with $f = A$ or $\deg(f - A) \le \Delta$,
$d_1(f)$ is $1$ if $f$ is monic and $0$ otherwise, $f$ is $B_\kappa$-free when no $P^{\kappa(P)}$
with $P$ monic irreducible divides it, and $P$ runs over the monic irreducible polynomials.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, case `h = 1` (`integers-2026-A80-thm-5`).
