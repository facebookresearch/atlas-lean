# Finite locally free group schemes and Cartier duality

This node is still to be broken down: the statements are precise, but their proofs are not.

Let $S$ be a scheme. A finite locally free group scheme over $S$ is a group scheme $G \to S$ whose
structure morphism is finite and locally free; its rank, the rank of the locally free
$\mathcal{O}_S$-module of its functions, is a locally constant function on $S$. A sequence $0 \to G'
\to G \to G'' \to 0$ of commutative finite locally free group schemes over $S$ is exact if it is
exact as a sequence of fppf sheaves. The targets are:

1. (Quotients and ranks.) Let $G$ be a commutative finite locally free group scheme over $S$ and $H
   \subset G$ a closed subgroup scheme that is finite locally free over $S$. The fppf quotient $G/H$
   is represented by a finite locally free group scheme, $G \to G/H$ is faithfully flat, and
   $\operatorname{rk} G = \operatorname{rk} H \cdot \operatorname{rk}(G/H)$. Consequently, if $f
   \colon G \to G''$ is a homomorphism of commutative finite locally free group schemes whose kernel
   $K$ is finite locally free with $\operatorname{rk} G = \operatorname{rk} K \cdot
   \operatorname{rk} G''$, then $f$ is an epimorphism of fppf sheaves and induces $G/K \cong G''$.
2. (Cartier duality.) For a commutative finite locally free group scheme $G$ over $S$, the fppf
   sheaf $G^D = \underline{\operatorname{Hom}}(G, \mathbb{G}_m)$ is represented by a commutative
   finite locally free group scheme of the same rank, whose functions are the $\mathcal{O}_S$-dual
   of those of $G$; the canonical map $G \to (G^D)^D$ is an isomorphism; and $G \mapsto G^D$ takes
   an exact sequence $0 \to G' \to G \to G'' \to 0$ to an exact sequence $0 \to G''^D \to G^D \to
   G'^D \to 0$.

The page on [p-divisible groups](p-divisible-group.md) uses them as follows. For a $p$-divisible
group $(G_i)$ of height $h$, multiplication by $p^s$ on $G_{j+s}$ has kernel $G_{j+s}[p^s] = G_s$
and image in $G_{j+s}[p^j] = G_j$, and $\operatorname{rk} G_{j+s} = \operatorname{rk} G_s \cdot
\operatorname{rk} G_j$, so item 1 makes it an epimorphism $G_{j+s} \to G_j$ and gives the exact
sequences $0 \to G_s \to G_{j+s} \to G_j \to 0$ (Chai–Oort, (1.18)); item 2 dualizes them into the
exact sequences that define the Serre dual (Chai–Oort, (1.20)). These arguments hold for every
$p$-divisible group, for instance $\mu_{p^\infty}$, of height $1$, which is not the $p$-divisible
group of an abelian scheme.

A good expansion has pages for: the representability of $G^D$ by the dual of the Hopf algebra of $G$
and biduality (Oort, I.2); the existence of fppf quotients of finite locally free group schemes by
finite locally free closed subgroups, with the multiplicativity of ranks; and the exactness of
Cartier duality (Tate, §§1.2–1.3).

## Depends on

Its statement uses fppf sheaves of groups, their quotients and the sheaf
$\underline{\operatorname{Hom}}(G, \mathbb{G}_m)$, which no page states yet.

## Proof depends on

The steps of its proof are not pages yet: the representability of the Cartier dual and biduality,
the existence of fppf quotients by finite locally free subgroups with the multiplicativity of
ranks, and the exactness of Cartier duality (Oort, I.2; Tate, §§1.2–1.3).

## Sources

- J. Tate, "p-divisible groups", in *Proceedings of a Conference on Local Fields* (Driebergen,
  1966), Springer, 1967, 158–183: §§1.2–1.3 (finite locally free commutative group schemes, their
  orders in exact sequences and Cartier duality), §2.1 (the exact sequences of a $p$-divisible
  group) and §2.3 (its dual).
- F. Oort, *Commutative Group Schemes*, Lecture Notes in Mathematics 15, Springer, 1966: I.2
  (Cartier duality), as cited by Chai and Oort, (1.20).
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (1.18)
  (the remark on the surjections and exact sequences of the finite stages) and (1.20) (the Serre
  dual through Cartier duality).
