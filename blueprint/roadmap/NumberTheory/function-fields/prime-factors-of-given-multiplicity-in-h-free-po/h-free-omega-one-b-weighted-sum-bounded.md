# Weighted coefficient bound for $B_{1,S_h}$

Let $F$ be a finite field with $q$ elements,
let $h \ge 2$ be a natural number, and let $A$ and $\sigma > 1/2$ be real numbers. Let $S_h$ be
the set of $h$-free monic polynomials over $F$ (those divisible by no $P^h$ with $P$ monic
irreducible) and $\omega_1(f)$ the number of distinct monic irreducible factors of $f$ of
multiplicity exactly $1$. For a complex number $z$ and a natural number $a$ let $B_z(a)$ be the
coefficient of $u^a$ in the formal power series

$$B_{1,S_h}(u, z) = (1 - qu)^z \sum_{f \in S_h} z^{\omega_1(f)} u^{\deg f},$$

where $(1 - qu)^z = \sum_{m \ge 0} \binom{z}{m} (-qu)^m$. Then there is a real constant $c$ such
that for every complex number $z$ with $|z| \le A$ and every natural number $n \ge 2$,

$$\sum_{a=0}^{n} |B_z(a)|\, q^{-\sigma a} \le c.$$

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Lemma 2.
