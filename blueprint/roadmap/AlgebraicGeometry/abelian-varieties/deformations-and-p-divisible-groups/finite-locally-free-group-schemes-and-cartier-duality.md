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
3. (Line bundles on quotients.) Let $G$ be a commutative finite locally free group scheme over $S$
   acting freely on an $S$-scheme $X$ with structure morphism $\pi \colon X \to S$, such that the
   fppf quotient $p \colon X \to Y = X / G$ is a scheme and $(\pi_T)_* \mathcal{O}_{X_T} =
   \mathcal{O}_T$ for every $S$-scheme $T$. Then for every $S$-scheme $T$ there is a canonical
   isomorphism, compatible with base change in $T$, from the group of isomorphism classes of line
   bundles $L$ on $Y_T$ with $p_T^* L \cong \mathcal{O}_{X_T}$ to $G^D(T)$; it sends $L$ to the
   character by which $G$ acts on a trivialization of $p_T^* L$.

The page on [p-divisible groups](p-divisible-group.md) uses them as follows. For a $p$-divisible
group $(G_i)$ of height $h$, multiplication by $p^s$ on $G_{j+s}$ has kernel $G_{j+s}[p^s] = G_s$
and image in $G_{j+s}[p^j] = G_j$, and $\operatorname{rk} G_{j+s} = \operatorname{rk} G_s \cdot
\operatorname{rk} G_j$, so item 1 makes it an epimorphism $G_{j+s} \to G_j$ and gives the exact
sequences $0 \to G_s \to G_{j+s} \to G_j \to 0$ (Chai–Oort, (1.18)); item 2 dualizes them into the
exact sequences that define the Serre dual (Chai–Oort, (1.20)). These arguments hold for every
$p$-divisible group, for instance $\mu_{p^\infty}$, of height $1$, which is not the $p$-divisible
group of an abelian scheme. The pages on the [dual abelian variety](../dual-abelian-variety.md) and
the [dual abelian scheme](../dual-abelian-scheme.md) use 3 with $X = A$, $G = \operatorname{Ker}(f)$
and $Y = B$ for an isogeny $f \colon A \to B$, which is faithfully flat with $A \times_B A \cong A
\times_S \operatorname{Ker}(f)$, so that $B$ is the quotient, to identify the kernel of the dual
isogeny with $\operatorname{Ker}(f)^D$ (van der Geer–Moonen, Theorem (7.5)).

## Depends on

- [The fppf topology on schemes](../../grothendieck-topologies/fppf-topology-on-schemes.md), for the
  fppf sheaves of the statement
- [The topology induced on an over category](../../../CategoryTheory/sites-and-sheaves/topology-on-an-over-category.md),
  for the fppf site of schemes over $S$
- [The sheaf of morphisms between two sheaves](../../../CategoryTheory/sites-and-sheaves/sheaf-of-morphisms-of-sheaves.md),
  for the sheaf $\underline{\operatorname{Hom}}(G, \mathbb{G}_m)$, taken between sheaves of groups
  so that its sections are homomorphisms

## Proof depends on

- [Closed immersions are the proper monomorphisms](../../schemes-and-morphisms/zariski-s-main-theorem/closed-immersion-iff-proper-and-mono.md),
  for the converse in 1: the monomorphism $G / K \to G''$, a morphism of finite $S$-schemes, is
  proper, hence a closed immersion
- [Closed immersions preserving the rank over the base are isomorphisms](../../schemes-and-morphisms/closed-and-open-immersions/is-iso-of-is-closed-immersion-of-finrank.md),
  for the converse in 1: a closed immersion $G / K \to G''$ between finite locally free $S$-schemes
  of the same rank is an isomorphism
- [Spectra of commutative Hopf algebras](../../schemes-and-morphisms/affine-group-schemes-and-hopf-algebras/spec-of-commutative-hopf-algebras.md),
  for the group scheme $\operatorname{Spec}$ of the dual Hopf algebra over an affine open subscheme
  on which $G$ is finite free, the candidate for $G^D$ there (Oort, I.2); its identification with
  the character sheaf, the gluing and biduality are further steps

## Expansion

A good expansion has pages for: the affine model of $G^D$, the dual Hopf algebra of the coordinate
algebra $H$ of $G$ over an affine open $\operatorname{Spec} R$ of $S$ on which $H$ is finite free
(stated in the project as `CartierDual R H`, defined as `Module.Dual`,
MathlibExt/RingTheory/HopfAlgebra/CartierDual.lean:54–56, with its Hopf algebra structure
`CartierDual.instHopfAlgebra`, MathlibExt/RingTheory/HopfAlgebra/CartierDual.lean:1114–1118); the
identification of its spectrum with the character sheaf, the gluing of these local identifications
and biduality (Oort, I.2); the existence of fppf quotients of finite locally free group schemes by
finite locally free closed subgroups, with the multiplicativity of ranks (Stacks Project, Tag 07S7,
which applies to the action of $H$ on the affine $S$-scheme $G$); the exactness of Cartier duality
(Tate, §§1.2–1.3); and, for 3, where the quotient is assumed to be a scheme, the descent of line
bundles along the $G$-torsor $X \to Y$ (van der Geer–Moonen, (7.2)–(7.4)).

A good expansion also states and links:

- quotients of fppf sheaves of abelian groups, for the statement

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
