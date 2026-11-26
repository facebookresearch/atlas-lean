/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality

/-!
# Degree identifications and cup products

Let `G` be a group, `k` a commutative ring, and `A` a representation. An equality `h : p = q`
induces a canonical map `E_A(h) : H^p(G,A) → H^q(G,A)` from the homology isomorphism of the
inhomogeneous cochain complex. Successive identifications compose along the transitive
equality.

The cup morphism commutes with these identifications in either input. Changing the left degree
by `p = p'` changes the output by `p + q = p' + q`; changing the right degree by `q = q'`
changes the output by `p + q = p + q'`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `A` be a representation of a group `G` over a commutative ring `k`, `p,q,r : ℕ`, `h : p =
q`, and `h' : q = r`. The canonical maps `E_A(h) : H^p(G,A) → H^q(G,A)` induced by
`homologyIsoOfEq` satisfy `E_A(h) ≫ E_A(h') = E_A(h.trans h')`. -/
theorem homologyIsoOfEq_hom_comp
    (A : Rep k G) {p q r : ℕ} (h : p = q) (h' : q = r) :
    ((inhomogeneousCochains A).homologyIsoOfEq h).hom ≫
        ((inhomogeneousCochains A).homologyIsoOfEq h').hom =
      ((inhomogeneousCochains A).homologyIsoOfEq (h.trans h')).hom := by
  subst q
  subst r
  simp [HomologicalComplex.homologyIsoOfEq]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, `p,p',q : ℕ`, and `h
: p = p'`. For the canonical homology degree maps `E`, `(E_A(h) ⊗ 𝟙) ≫ cup G k A B p' q = cup
G k A B p q ≫ E_{A⊗B}(congrArg (fun r => r + q) h)`, as maps into `H^{p'+q}(G,A ⊗ B)`. -/
theorem cup_left_degree_transport
    (A B : Rep k G) {p p' : ℕ} (h : p = p') (q : ℕ) :
    (((inhomogeneousCochains A).homologyIsoOfEq h).hom ⊗ₘ
          𝟙 (groupCohomology B q)) ≫
        cup G k A B p' q =
      cup G k A B p q ≫
        ((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
          (congrArg (fun r => r + q) h)).hom := by
  cases h
  simp only [HomologicalComplex.homologyIsoOfEq, Iso.refl_hom,
    tensorHom_id, id_whiskerRight, Category.id_comp]
  exact (Category.comp_id (cup G k A B p q)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, `p,q,q' : ℕ`, and `h
: q = q'`. For the canonical homology degree maps `E`, `(𝟙 ⊗ E_B(h)) ≫ cup G k A B p q' = cup
G k A B p q ≫ E_{A⊗B}(congrArg (fun r => p + r) h)`, as maps into `H^{p+q'}(G,A ⊗ B)`. -/
theorem cup_right_degree_transport
    (A B : Rep k G) (p : ℕ) {q q' : ℕ} (h : q = q') :
    (𝟙 (groupCohomology A p) ⊗ₘ
          ((inhomogeneousCochains B).homologyIsoOfEq h).hom) ≫
        cup G k A B p q' =
      cup G k A B p q ≫
        ((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq
          (congrArg (fun r => p + r) h)).hom := by
  cases h
  simp only [HomologicalComplex.homologyIsoOfEq, Iso.refl_hom,
    id_tensorHom, whiskerLeft_id, Category.id_comp]
  exact (Category.comp_id (cup G k A B p q)).symm

end groupCohomology
