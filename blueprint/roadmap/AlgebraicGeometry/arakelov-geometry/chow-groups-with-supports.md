# Chow groups with supports and their products

This node is still to be broken down. It covers the algebraic intersection theory on which the
[arithmetic intersection product](arithmetic-intersection-product.md) rests: Chow groups with
supports, their products on regular schemes, and the moving lemmas used to bring cycles into proper
position.

Let $X$ be a noetherian scheme and $Y \subseteq X$ a closed subset. The group $Z^p_Y(X)$ of cycles
of codimension $p$ with supports in $Y$ is the free abelian group on the integral subschemes of $X$
of codimension $p$ in $X$ contained in $Y$, and the Chow group with supports $CH^p_Y(X)$ is its
quotient by the divisors $\operatorname{div}(f)$ of rational functions $f \in k(W)^\times$ on
integral subschemes $W$ of codimension $p - 1$ in $X$ contained in $Y$. There is an exact sequence
$CH^p_Y(X) \to CH^p(X) \to CH^p(X \setminus Y) \to 0$. For a family of supports $\Phi$, a family of
closed subsets stable under finite unions, $CH^p_\Phi(X)$ is the direct limit of the $CH^p_Y(X)$
over $Y \in \Phi$. These definitions need no regularity.

Now let $X$ be a separated regular noetherian scheme of finite Krull dimension $d$. Then
$CH^p_Y(X)_\mathbb{Q} \cong \mathrm{Gr}^p_\gamma K_0^Y(X)_\mathbb{Q}$, the graded piece of the
$\gamma$-filtration on the rationalized Grothendieck group of bounded complexes of locally free
sheaves on $X$ acyclic off $Y$ (Gillet and Soulé, *Intersection theory using Adams operations*,
Theorem 8.2, where, for $d \ge 1$, the isomorphism holds after inverting $(d - 1)!$; Soulé, Theorem
4). Through it the product of $K$-theory gives products $CH^p_Y(X)_\mathbb{Q} \otimes
CH^q_Z(X)_\mathbb{Q} \to CH^{p+q}_{Y \cap Z}(X)_\mathbb{Q}$ for all closed subsets $Y$ and $Z$
(Theorem C), and, by taking limits, products $CH^p_\Phi(X)_\mathbb{Q} \otimes
CH^q_\Psi(X)_\mathbb{Q} \to CH^{p+q}_{\Phi \cap \Psi}(X)_\mathbb{Q}$, where $\Phi \cap \Psi$ is the
family of finite unions of sets $Y \cap Z$ with $Y \in \Phi$, $Z \in \Psi$. If $Y$ and $Z$ are
integral and intersect properly, the product of their classes is $\sum_i m_i [W_i]$ over the
components $W_i$ of $Y \cap Z$, with Serre's intersection multiplicities $m_i = \sum_j (-1)^j
\operatorname{length} \operatorname{Tor}_j^{\mathcal{O}_{X, W_i}} (\mathcal{O}_Y, \mathcal{O}_Z)$
(Theorem C). For $X$ smooth over a field the product exists with integral coefficients
(Gillet–Soulé, *Arithmetic intersection theory*, Remark 4.1.2).

Gillet and Soulé's moving lemma for $K_1$-chains (4.2.6): let $X$ be a smooth quasi-projective
variety over an infinite field and $\mathcal{Z}$ a finite set of subvarieties; if $f$ is a
$K_1$-chain whose divisor meets the members of $\mathcal{Z}$ properly, there is a $K_1$-chain $g$
with $\operatorname{div}(g) = \operatorname{div}(f)$, $g - f$ a boundary, and $g$ meeting
$\mathcal{Z}$ almost properly: the divisor of each summand meets $\mathcal{Z}$ properly, though its
support need not.

## Depends on

- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the variety convention in the moving-lemma case; smoothness and quasi-projectivity are
  hypotheses of that lemma

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for:

- Chow groups with supports in a closed subset and in a family of supports, with the exact sequence
  above (Gillet–Soulé, 4.1.1);
- $K$-theory with supports, its $\lambda$-operations and $\gamma$-filtration, and the isomorphism
  above (Soulé, §5.2, Theorem 4, and the remark on supports; Gillet and Soulé, *Adams operations*,
  §1.2 and Theorem 8.2);
- the products of Chow groups with supports on a regular scheme of finite Krull dimension and their
  agreement with Serre's Tor formula for cycles that intersect properly (Gillet and Soulé, *Adams
  operations*, Theorem C; Serre, *Algèbre locale, multiplicités*, Chapter V);
- Chow's moving lemma for cycles on smooth quasi-projective varieties (Roberts), and the moving
  lemma for $K_1$-chains above, which the proof of the arithmetic intersection product uses on the
  generic fibre (Gillet–Soulé 4.2.5–4.2.6 and p. 143).

A good expansion also states and links:

- the Grothendieck group of complexes of locally free sheaves acyclic off a closed subset, with its
  $\gamma$-filtration, and $K_1$-chains (Gillet–Soulé, *Adams operations*, §1.2; Gillet–Soulé,
  4.2.5), for the statement

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: 4.1.1 (Chow groups with supports, the
  isomorphism with the graded $K$-theory with supports for regular $X$, products, Serre's Tor
  formula, families of supports, pp. 136–137), Remark 4.1.2 (integral coefficients over a field, p.
  137), 4.2.5–4.2.6 (moving lemma for $K_1$-chains, pp. 140–143) and the moving lemma for cycles, p. 143.
- C. Soulé, "Opérations en K-théorie algébrique", Canad. J. Math. 37 (1985), 488–550: §5.2, Theorem
  4, p. 521 (regular noetherian schemes of finite Krull dimension), and the remark on supports, p. 526.
- H. Gillet and C. Soulé, "Intersection theory using Adams operations", Invent. Math. 90 (1987),
  243–277: conventions (separated noetherian schemes) and §1.2, p. 245; Theorem 8.2, p. 274; Theorem
  C, p. 276.
- J.-P. Serre, *Algèbre locale, multiplicités*, Lecture Notes in Mathematics 11, Springer, 3rd ed.,
  1975: Chapter V (intersection multiplicities by the Tor formula), as cited by Gillet and Soulé.
- J. Roberts, "Chow's moving lemma", in *Algebraic Geometry, Oslo 1970* (F. Oort, ed.),
  Wolters-Noordhoff, Groningen, 1972, 89–96, as cited by Gillet and Soulé.
