# p-divisible group

Let $p$ be a prime and $S$ a scheme. A **$p$-divisible group** (or Barsotti–Tate group) over $S$ is
an inductive system $X = (G_i)_{i \ge 1}$ of commutative finite locally free group schemes $G_i \to S$,
with inclusions $G_i \subset G_{i+1}$ such that $G_{i+1}[p^i] = G_i$ for every $i$, and a locally
constant function $h \colon S \to \mathbb{Z}_{\ge 0}$, the **height**, such that $G_i$ has rank
$p^{i h(s)}$ near every point $s$. Multiplication by $p^s$ then induces epimorphisms of fppf sheaves
$G_{j+s} \to G_j$, and there are exact sequences of fppf sheaves of finite flat group schemes
$0 \to G_i \to G_{i+s} \to G_s \to 0$. Homomorphisms of $p$-divisible groups are
$\operatorname{Hom}((G_i), (H_j)) = \varprojlim_i \varinjlim_j \operatorname{Hom}(G_i, H_j)$. Over a
connected base the height is a constant $h \ge 0$; Chai and Oort fix $h > 0$, but the abelian scheme
$A = S$ of relative dimension $0$ gives $h = 0$, and over a disconnected base the height can differ
from one component to another.

For an [abelian scheme](abelian-scheme.md) $A \to S$ of relative dimension $g$, a locally constant
function, the kernels $A[p^i]$ of multiplication by $p^i$, which are finite locally free of rank
$p^{2gi}$ by the theorem on [isogenies of abelian schemes](isogenies-of-abelian-schemes.md), form a
$p$-divisible group $A[p^\infty]$ of height $2g$, and a homomorphism of abelian schemes induces a
homomorphism of their $p$-divisible groups.

The **Serre dual** of $X = (G_i)$ is the $p$-divisible group $X^t = (G_i^D)$ of the Cartier duals,
with the inclusions $G_s^D \hookrightarrow G_{s+1}^D$ dual to the surjections
$G_{s+1} \to G_s$. For an abelian scheme with [dual abelian scheme](dual-abelian-scheme.md) $A^t$, the
duality of the kernels of isogenies gives $(A[p^\infty])^t = A^t[p^\infty]$.

## Depends on

- [Abelian scheme](abelian-scheme.md), for the $p$-divisible group of an abelian scheme
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for the finite flat kernels
  $A[p^i]$ and their ranks
- [Dual abelian scheme](dual-abelian-scheme.md), for $A^t$ and the duality of kernels of isogenies

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (1.18)
  (definition for a fixed height $h > 0$, the remark on the exact sequences, the example $A[p^\infty]$
  and homomorphisms), (1.10) and (1.20) (Serre dual, and $(A[p^\infty])^t = A^t[p^\infty]$), (2.6)–(2.7)
  (abelian schemes over $S$ without restriction on the dimension) and (10.11) (group schemes are taken
  commutative).
- J. Tate, "p-divisible groups", in *Proceedings of a Conference on Local Fields* (Driebergen, 1966),
  Springer, 1967, 158–183: §2.1 (height $h \ge 0$).
