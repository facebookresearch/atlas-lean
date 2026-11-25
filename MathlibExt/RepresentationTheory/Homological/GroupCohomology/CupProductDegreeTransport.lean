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
# Degree transport for group-cohomology cup products

The arbitrary cup commutes with transporting either input degree along an
equality.  These lemmas make arithmetic reassociation of cup products
available without exposing dependent casts in consumers.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Successive degree transports on group cohomology compose to transport
along the transitive equality. -/
theorem homologyIsoOfEq_hom_comp
    (A : Rep k G) {p q r : ℕ} (h : p = q) (h' : q = r) :
    ((inhomogeneousCochains A).homologyIsoOfEq h).hom ≫
        ((inhomogeneousCochains A).homologyIsoOfEq h').hom =
      ((inhomogeneousCochains A).homologyIsoOfEq (h.trans h')).hom := by
  subst q
  subst r
  simp [HomologicalComplex.homologyIsoOfEq]

set_option backward.isDefEq.respectTransparency.types false in
/-- Transporting the left input degree before cupping is transport of the
output degree after cupping. -/
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
/-- Transporting the right input degree before cupping is transport of the
output degree after cupping. -/
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
