# Constant coefficient of $B_{1,S_h}$

Let $F$ be a finite field with $q$ elements and let
$h \ge 1$ be a natural number. Let $S_h$ be the set of $h$-free monic polynomials over $F$ (those
divisible by no $P^h$ with $P$ monic irreducible) and $\omega_1(f)$ the number of distinct monic
irreducible factors of $f$ of multiplicity exactly $1$. For every complex number $z$, the
coefficient $B_z(0)$ of $u^0$ in the formal power series

$$B_{1,S_h}(u, z) = (1 - qu)^z \sum_{f \in S_h} z^{\omega_1(f)} u^{\deg f},$$

where $(1 - qu)^z = \sum_{m \ge 0} \binom{z}{m} (-qu)^m$, equals $1$.

The only monic polynomial of degree $0$ is $1$, which is $h$-free and has $\omega_1(1) = 0$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Section 3.1 (definition preceding Lemma 2).
