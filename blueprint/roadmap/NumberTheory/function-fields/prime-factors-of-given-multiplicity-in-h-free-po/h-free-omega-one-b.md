# Coefficients of $B_{1,S_h}(u, z)$

Let $F$ be a finite field with $q$ elements, let $h$
be a natural number and let $z$ be a complex number. Let $S_h$ be the set of $h$-free monic
polynomials over $F$ (those divisible by no $P^h$ with $P$ monic irreducible), and $\omega_1(f)$
the number of distinct monic irreducible factors of $f$ of multiplicity exactly $1$. Write
$C_{1,S_h}(u, z) = \sum_{f \in S_h} z^{\omega_1(f)} u^{\deg f}$ and
$B_{1,S_h}(u, z) = Z_q(u)^{-z} C_{1,S_h}(u, z)$, where $Z_q(u)^{-z} = (1 - qu)^z$ is the power
series with coefficient $q^m (-z)_m / m!$ at $u^m$ and $(x)_m = x(x+1) \cdots (x+m-1)$ is the
rising factorial. For a natural number $n$, $B_z(n)$ is the coefficient of $u^n$ in
$B_{1,S_h}(u, z)$, that is,

$$B_z(n) = \sum_{a=0}^{n} \Bigl(\sum_{f \in S_h,\ \deg f = a} z^{\omega_1(f)}\Bigr)
\frac{q^{n-a} (-z)_{n-a}}{(n-a)!}.$$

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Section 3.1 (definition preceding Lemma 2).
