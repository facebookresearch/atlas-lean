# Divisor sums over $B_\kappa$-free polynomials in short intervals

Let $F$ be a finite field
with $q$ elements and let $\kappa$ assign to each polynomial in $F[T]$ a natural number, with
$\kappa(P) \ge 2$ for every monic irreducible $P$. Suppose that $\kappa$ is symmetric:
$\kappa(P^*) = \kappa(P)$ for every monic irreducible $P$ with $P(0) \ne 0$, where $P^*$ is the
monic scalar multiple of $T^{\deg P} P(1/T)$. Let $h \ge 1$ be an integer, let $c$ be a real
number with $c > (h + 2/\kappa_{\min})/(h + 2)$, and let $\varepsilon > 0$. Then there is a constant
$C$ such that for every sufficiently large $N$, every monic $A \in F[T]$ of degree $N$ and every
integer $\Delta$ with $cN \le \Delta \le N - 2$,

$$
\left| \tilde N_{B_\kappa,h}(A, \Delta) - q^{-(N - \Delta - 1)} \left( \tilde D_{B_\kappa,h}(N) -
\tilde D_{B_\kappa,h}(N - 1) \right) \right| \le
C q^{h (N - \Delta)/2 + (1/\kappa_{\min} + \varepsilon) N}.
$$

Here $\tilde N_{B_\kappa,h}(A, \Delta)$ is the sum of $d_h(f)$ over the $B_\kappa$-free
$f \in F[T]$ with $\deg(f - A) \le \Delta$ (where $\deg 0 = -\infty$), $d_h(f)$ is the number of
$h$-tuples of monic polynomials with product $f$, $\tilde D_{B_\kappa,h}(N)$ is the sum of $d_h(f)$
over the $B_\kappa$-free monic $f$ of degree at most $N$, and $\kappa_{\min}$ is the minimum of
$\kappa(P)$ over the monic irreducible $P$.

The paper's $\kappa(P^*)$ leaves $P^*$ unnormalized and undefined for $P = T$.

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, general formula.
