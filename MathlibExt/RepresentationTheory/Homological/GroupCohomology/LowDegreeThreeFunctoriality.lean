/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Functoriality for explicit degree-three group cohomology

This file extends the explicit low-degree-three API with cochain, cocycle,
and `H3π` naturality under a group homomorphism and equivariant coefficient
map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Representation

universe u

namespace groupCohomology

open ShortComplex

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A : Rep k H} {B : Rep k G}
variable (f : G →* H) (φ : Rep.res f A ⟶ B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem isoCocycles₃_hom_comp_i (A : Rep k G) :
    (isoCocycles₃ A).hom ≫
        (shortComplexH3 A).moduleCatLeftHomologyData.i =
      iCocycles A 3 ≫ (cochainsIso₃ A).hom := by
  simp [isoCocycles₃, iCocycles, HomologicalComplex.iCycles, iCycles]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem isoCocycles₃_inv_comp_iCocycles (A : Rep k G) :
    (isoCocycles₃ A).inv ≫ iCocycles A 3 =
      (shortComplexH3 A).moduleCatLeftHomologyData.i ≫ (cochainsIso₃ A).inv :=
  (CommSq.horiz_inv ⟨isoCocycles₃_hom_comp_i A⟩).w

/-- Degree-four inhomogeneous cochain map in explicit coordinates. -/
noncomputable abbrev cochainsMap₄ :
    ModuleCat.of k (H × H × H × H → A) ⟶
      ModuleCat.of k (G × G × G × G → B) :=
  ModuleCat.ofHom <| φ.hom.toLinearMap.compLeft (G × G × G × G) ∘ₗ
    LinearMap.funLeft k A
      (Prod.map f (Prod.map f (Prod.map f f)))

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cochainsMap_f_4_comp_cochainsIso₄ :
    (cochainsMap f φ).f 4 ≫ (cochainsIso₄ B).hom =
      (cochainsIso₄ A).hom ≫ cochainsMap₄ f φ := by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Explicit map of short complexes computing degree-three cohomology. -/
@[simps]
noncomputable def mapShortComplexH3 :
    shortComplexH3 A ⟶ shortComplexH3 B where
  τ₁ := cochainsMap₂ f φ
  τ₂ := cochainsMap₃ f φ
  τ₃ := cochainsMap₄ f φ
  comm₁₂ := by
    ext x
    funext g
    simp [shortComplexH3, ← Rep.hom_comm_apply φ]
  comm₂₃ := by
    ext x
    funext g
    simp [shortComplexH3, d₃₄, ← Rep.hom_comm_apply φ]

/-- Map on explicit degree-three cocycles. -/
noncomputable abbrev mapCocycles₃ :
    ModuleCat.of k (cocycles₃ A) ⟶ ModuleCat.of k (cocycles₃ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH3 f φ)
    (shortComplexH3 A).moduleCatLeftHomologyData
    (shortComplexH3 B).moduleCatLeftHomologyData

@[simp]
theorem coe_mapCocycles₃ (x) :
    ⇑(mapCocycles₃ f φ x) = cochainsMap₃ f φ x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem cocyclesMap_comp_isoCocycles₃_hom :
    cocyclesMap f φ 3 ≫ (isoCocycles₃ B).hom =
      (isoCocycles₃ A).hom ≫ mapCocycles₃ f φ := by
  simp [← cancel_mono
      (shortComplexH3 B).moduleCatLeftHomologyData.i,
    mapShortComplexH3, cochainsMap_f_3_comp_cochainsIso₃ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem H3π_comp_map :
    H3π A ≫ map f φ 3 = mapCocycles₃ f φ ≫ H3π B := by
  simp [H3π, Iso.inv_comp_eq,
    ← cocyclesMap_comp_isoCocycles₃_hom_assoc]

end groupCohomology
