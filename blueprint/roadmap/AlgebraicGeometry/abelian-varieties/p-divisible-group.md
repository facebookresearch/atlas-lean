# p-divisible group

Let $p$ be a prime, $h$ a positive integer and $S$ a scheme. A **$p$-divisible group** (or
Barsotti–Tate group) of height $h$ over $S$ is an inductive system $X = (G_i)_{i \ge 1}$ of
commutative finite flat group schemes $G_i \to S$ of rank $p^{ih}$, with inclusions
$G_i \subset G_{i+1}$ such that $G_{i+1}[p^i] = G_i$ for every $i$. Multiplication by $p^s$ then
induces surjections $G_{j+s} \to G_j$, and there are exact sequences of finite flat group schemes
$0 \to G_i \to G_{i+s} \to G_s \to 0$. Homomorphisms of $p$-divisible groups are
$\operatorname{Hom}((G_i), (H_j)) = \varprojlim_i \varinjlim_j \operatorname{Hom}(G_i, H_j)$.

For an [abelian scheme](abelian-scheme.md) $A \to S$ of relative dimension $g$, the kernels
$A[p^i]$ of multiplication by $p^i$ form a $p$-divisible group $A[p^\infty]$ of height $2g$, and a
homomorphism of abelian schemes induces a homomorphism of their $p$-divisible groups.

The **Serre dual** of $X = (G_i)$ is the $p$-divisible group $X^t = (G_i^D)$ of the Cartier duals,
with the inclusions $G_s^D \hookrightarrow G_{s+1}^D$ dual to the surjections
$G_{s+1} \to G_s$; for an abelian scheme with dual $A^t$, $(A[p^\infty])^t = A^t[p^\infty]$.

## Depends on

- [Abelian scheme](abelian-scheme.md), for the $p$-divisible group of an abelian scheme

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (1.18)
  (definition, the remark on the exact sequences, the example $A[p^\infty]$ and homomorphisms), (1.20)
  (Serre dual) and (10.11) (group schemes are taken commutative).
