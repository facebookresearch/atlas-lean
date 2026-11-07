# Perron's formula for monic polynomials over a finite field

Let $F$ be a finite field, let
$a$ be a complex-valued function on $F[T]$, and let $\rho$ be a real number with $0 < \rho < 1$ such
that the series $\sum_f |a(f)| \rho^{\deg f}$ over all monic $f \in F[T]$ converges. Put
$A(u) = \sum_f a(f) u^{\deg f}$, the sum again over all monic $f$. Then for every natural number
$n$, with the circle $|u| = \rho$ traversed counterclockwise,

$$\sum_{f \text{ monic},\ \deg f \le n} a(f) = \frac{1}{2 \pi i} \oint_{|u| = \rho}
\frac{A(u)}{u^n (1 - u)} \, \frac{du}{u}.$$

## Sources

- Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 1 (Perron's Formula) (`integers-2026-A80-lem-1`).
