/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerGeneratingCofibrations
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses
import MathlibExt.CategoryTheory.Functor.IsofibrationEssentialSurjectivity

/-!
# Actual Bergner generator right maps and the original weak/fibration classes

The local-fibration predicate uses every original scalar Kan fibration
and strict isomorphism lifting of the same original component functor,
as in HTT Definition A.3.2.9. The genuine global generating-cofibration
right class is exactly its intersection with the original changing-object
Dwyer–Kan weak class. No global model axioms or Quillen-equivalence
certificate are supplied or concluded here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- All actual scalar Hom fibrations and exact isomorphism lifting on the SAME original component functor. -/
def localFibrations : MorphismProperty Carrier.{u} := fun _ _ F =>
  (∀ x y, Fibration (F.map x y)) ∧ (ComponentCategory.mapFunctor F).IsIsofibration

private theorem scalar_boundary_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    SSet.modelCategoryQuillen.I.rlp p ↔ Fibration p ∧ SSet.realizationWeakEquivalences p := by
  constructor
  · intro hp
    have hm : (MorphismProperty.monomorphisms SSet.{u}).rlp p := by rwa [SSet.rlp_monomorphisms]
    have hJ := MorphismProperty.antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms p hm
    have hf := (SSet.modelCategoryQuillen.fibration_iff p).mpr hJ
    let _ : Fibration p := hf
    exact ⟨hf, (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mp hp⟩
  · rintro ⟨hf, hw⟩
    let _ : Fibration p := hf
    exact (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration p).mpr hw

/-- The actual global right class is literal original object surjectivity and genuine scalar trivial fibrations. -/
theorem generatingCofibrations_rlp_original_iff {C D : Carrier.{u}} (F : C ⟶ D) :
    generatingCofibrations.rlp F ↔ Function.Surjective F.obj ∧
      ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y) := by
  rw [generatingCofibrations_rlp_iff]
  exact and_congr_right (fun _ => forall_congr' (fun x => forall_congr' (fun y => scalar_boundary_iff (F.map x y))))

/-- Genuine original local fibrations that are DK weak have exact original object surjectivity and scalar trivial
fibrations. -/
theorem localFibrations_and_weak_original_iff {C D : Carrier.{u}} (F : C ⟶ D) :
    (localFibrations ⊓ EnrichedDwyerKan.weakEquivalences) F ↔ Function.Surjective F.obj ∧
      ∀ x y : C, Fibration (F.map x y) ∧ SSet.realizationWeakEquivalences (F.map x y) := by
  constructor
  · rintro ⟨hF, hW⟩
    let _ : (ComponentCategory.mapFunctor F).IsIsofibration := hF.2
    let _ : (ComponentCategory.mapFunctor F).EssSurj := hW.2
    exact ⟨Functor.surjective_obj_of_isIsofibration (ComponentCategory.mapFunctor F),
      fun x y => ⟨hF.1 x y, hW.1 x y⟩⟩
  · rintro ⟨hObj, hHom⟩
    have hW : EnrichedDwyerKan.weakEquivalences F :=
      ⟨fun x y => (hHom x y).2, Functor.essSurj_of_surj hObj⟩
    let _ : (ComponentCategory.mapFunctor F).IsEquivalence := EnrichedDwyerKan.componentIsEquivalence F hW
    have hIso : (ComponentCategory.mapFunctor F).IsIsofibration :=
      Functor.isIsofibration_of_isEquivalence_of_surjective _ hObj
    exact ⟨⟨fun x y => (hHom x y).1, hIso⟩, hW⟩

/-- The SAME actual generating-cofibration right class is the exact original weak/local-fibration intersection. -/
theorem generatingCofibrations_rlp_eq_localFibrations_inf_weak :
    generatingCofibrations.{u}.rlp = localFibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  ext C D F
  exact (generatingCofibrations_rlp_original_iff F).trans (localFibrations_and_weak_original_iff F).symm

/-- Every original generator-right map is genuinely DK weak on its SAME original objects and Hom maps. -/
theorem generatingCofibrations_right_weak {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : generatingCofibrations.rlp F) : EnrichedDwyerKan.weakEquivalences F := by
  rw [generatingCofibrations_rlp_eq_localFibrations_inf_weak] at hF
  exact hF.2

/-- Every original generator-right map is an actual local fibration of the SAME changing-object enrichment. -/
theorem generatingCofibrations_right_localFibration {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : generatingCofibrations.rlp F) : localFibrations F := by
  rw [generatingCofibrations_rlp_eq_localFibrations_inf_weak] at hF
  exact hF.1

end CategoryTheory.SimplicialEnrichment.Bergner
