# The global Artin map on the Galois group of the maximal abelian extension

This node is still to be broken down. It covers the properties of the
[global Artin map](global-artin-map.md) $\phi_K \colon \mathbb{I}_K \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ of a
number field $K$ that concern the whole group $\mathrm{Gal}(K^{\mathrm{ab}}/K)$, beyond the
[global reciprocity law](global-reciprocity-law.md) for each finite abelian extension. Fix an algebraic
closure $\overline{K}$, let $K^{\mathrm{ab}} \subseteq \overline{K}$ be the maximal abelian extension of $K$, and
for an infinite place $v$ let $K_v^{\times,0}$ be the identity component of $K_v^\times$ ($\mathbb{C}^\times$ or
$\mathbb{R}_{>0}$), viewed in $\mathbb{I}_K$. It contains the following statements.

1. **Surjectivity and openness.** $\phi_K$ is surjective and open (Milne, Remark V.5.7(a) and Summary
   V.5.10; Sutherland, Remark 28.5). Its image is dense, because every $\phi_{L/K}$ is surjective, and
   closed, because $\phi_K$ is trivial on $K^\times$ and on $\prod_{v \mid \infty} K_v^{\times,0}$, so that its
   image is the image of the norm-one idèle class group $\mathbb{I}_K^1 / K^\times$, which is compact (Milne,
   4.4 of Chapter V, which states this compactness, and Remark V.4.11, which gives this argument for the
   ray class groups). Openness then follows from the open mapping theorem for $\sigma$-compact locally
   compact groups.
2. **The kernel.** The kernel of $\phi_K$ is the closure of $K^\times \prod_{v \mid \infty} K_v^{\times,0}$,
   whose image in the idèle class group $C_K = \mathbb{I}_K / K^\times$ is the identity component of $C_K$
   (Milne, Remark V.5.7(a), which states it without proof; Sutherland, Remark 28.5). The kernel contains
   this closure because it is closed. By the [existence theorem](../existence-theorem/existence-of-class-fields.md),
   the kernel is the intersection of the open subgroups of finite index of $\mathbb{I}_K$ that contain
   $K^\times$; the remaining input is that this intersection is no larger than the closure above, a
   statement about the topology of $C_K$.
3. **Local behaviour at the finite places.** Let $v$ be a finite place of $K$, $q_v$ the order of its
   residue field, $w$ a place of $K^{\mathrm{ab}}$ above $v$, and $I_w \subseteq D_w$ the inertia and
   decomposition groups of $w$ in $\mathrm{Gal}(K^{\mathrm{ab}}/K)$; a Frobenius element of $w$ is an element of
   $D_w$ that induces $x \mapsto x^{q_v}$ on the residue field of $w$. Then
   $\phi_K(\mathcal{O}_v^\times) = I_w$, the closure of $\phi_K(K_v^\times)$ is $D_w$, and the elements
   $\phi_K(\pi)$, for $\pi$ running through the uniformizers of $K_v$, are exactly the Frobenius elements
   of $w$. This comes from the definition of $\phi_K$ through the local Artin maps (Milne, Proposition
   V.5.2 and Summary V.5.10) and from local class field theory: the local Artin map of $K_v$ has dense
   image and maps the units onto the inertia subgroup of $\mathrm{Gal}(K_v^{\mathrm{ab}}/K_v)$ (Sutherland,
   Theorem 27.9 and the diagram after it).

The reciprocal map $a \mapsto \phi_K(a)^{-1}$ has the same properties, with every Frobenius element replaced
by its inverse, a geometric Frobenius element; this is the normalization of the map $\mathrm{Art}_K$ on the
page of [the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), applied to the global
map.

A good expansion has a page for each numbered item. Item 1 needs a page for the compactness of the
norm-one idèle class group, item 2 one for the identity component of $C_K$ as the intersection of its
open subgroups of finite index, and item 3 one for the units and the inertia subgroup in local class field
theory.

## Depends on

- [Global Artin map](global-artin-map.md)

## Proof depends on

- [Global reciprocity law](global-reciprocity-law.md), for the dense image in item 1 and the triviality on $K^\times$
- [Norm-one idele class group](../adeles-and-ideles/norm-one-idele-class-group.md), for the compact group whose image is that of $\phi_K$, in item 1
- [Existence theorem of global class field theory](../existence-theorem/existence-of-class-fields.md), for the kernel in item 2
- [Local class field theory: the local Artin map](../../../p-adic-numbers/local-class-field-theory.md), for item 3

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Remark V.5.7(a) (surjectivity, and the kernel
  "is precisely" the closure of $K^\times \prod_{v \mid \infty} K_v^{+}$, stated without proof); Summary
  V.5.10 (a continuous surjective homomorphism); 4.4 and Remark 4.11 of Chapter V (the compactness of
  $\mathbb{I}^1/K^\times$, stated, and the density-and-compactness argument for the ray class groups);
  Proposition V.5.2 (the global map as the product of the local ones).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28, "Global class field theory,
  the Chebotarev density theorem", <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>:
  Remark 28.5 (for a number field the global Artin map is surjective, with kernel the connected component
  of the identity); Lecture 27, "Local class field theory",
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes27.pdf>: Theorem 27.9 and the diagram after it
  (the units correspond to the inertia subgroup).
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the open
  mapping theorem used in item 1: `MonoidHom.isOpenMap_of_sigmaCompact`,
  https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Algebra/Group/OpenMapping.lean#L114-L117.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states items 1 to 3 for the reciprocal map, with the
  inverse of the Frobenius elements, as `GlobalTheory.Published.GlobalArtinReciprocity` (the structure
  `GlobalTheory.HeckeGal.IsGlobalArtin`), and proves it for the inverse of its arithmetic Artin map in
  `CompanionTheory.FamInh.isGlobalArtin_inv`.
