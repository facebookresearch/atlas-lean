# The coefficients $B_z(n)$ of the $h$-full series

Let $F$ be a finite field with $q$
elements, let $h$ and $n$ be natural numbers and let $z$ be a complex number. Write $N_h$ for the
set of $h$-full monic polynomials over $F$ (monic $f$ such that $P^h$ divides $f$ for every monic
irreducible $P$ dividing $f$), $\omega_h(f)$ for the number of monic irreducible polynomials that
divide $f$ with multiplicity exactly $h$, and $(x)_m = x(x + 1) \cdots (x + m - 1)$ for the
rising factorial. For $0 \le a \le n$ let $c_a = \sum_f z^{\omega_h(f)}$, the sum over the
$f \in N_h$ of degree $a$. Then $B_z(n)$ is the sum of $c_a \, q^m (-z)_m / m!$ over the $a$ with
$0 \le a \le n$ and $h \mid n - a$, where $m = (n - a)/h$; when $h = 0$ only $a = n$ occurs, with
$m = 0$.

For $h \ge 1$, $B_z(n)$ is the coefficient of $u^n$ in
$B_{h,N_h}(u, z) = (1 - qu^h)^z \sum_{f \in N_h} z^{\omega_h(f)} u^{\deg f}$, since $(1 - qu^h)^z$
has coefficient $q^m (-z)_m / m!$ at $u^{hm}$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Section 4.1 (definition preceding Lemma 4).
