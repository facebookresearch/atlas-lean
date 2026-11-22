/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerIntervalFamily
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedInitialObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWeakUnitHomsPointRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerEquivalenceVertexLifting

/-!
# Genuine small original A2 maps and their full original cofibration/weak classes

The actual small representative property consists only of the proved
original countable, fixed-cofibrant, weak-unit two-label intervals. Each
SAME original point inclusion is genuinely C0 cofibrant and Dwyer--Kan
weak. The full original A1+A2 generator family is small, keeping every
original positive horn and original representative point map.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
attribute [local instance] FixedObjectModel.modelCategory

/-- The SAME original full point inclusion at either literal original interval label. -/
abbrev pointMap (H : FixedObjects walking.{u}) (x : walking.{u}) : BergnerObjects.point.{u} ⟶ H.val :=
  BergnerObjects.select (vertex H x)

/-- Every actual original representative point map is genuinely cofibrant in the original global C0 class. -/
theorem point_cofibration (H : FixedObjects walking.{u}) (hH : representatives H) (x : walking.{u}) :
    Bergner.cofibrations (pointMap H x) := by
  let _ : ModelCategory (FixedObjects walking.{u}) := FixedObjectModel.modelCategory walking
  have h := representative_interval H hH
  let _ : IsCofibrant H := h.2.2.1
  have hi : FixedObjectModel.cofibrations walking (initial.to H) :=
    (FixedObjectModel.cofibration_iff_freeBoundary (initial.to H)).mp
      (inferInstance : Cofibration (initial.to H))
  have hg := Bergner.fixedCofibration_global (initial.to H) hi
  have hc := Bergner.cofibrations.comp_mem _ _ (BergnerFixedInitialObjects.point_cofibration walking x) hg
  have hp : BergnerObjects.select (BergnerFixedInitialObjects.vertex walking x) ≫
      (initial.to H).val = pointMap H x := by
    exact (BergnerObjects.select_comp _ _).trans
      (congrArg BergnerObjects.select (map_vertex (initial.to H) x))
  exact (congrArg (fun f => Bergner.cofibrations f) hp).mp hc

/-- Every actual original representative has ALL full original Hom unit maps genuinely weak. -/
theorem representative_hom_weak (H : FixedObjects walking.{u}) (hH : representatives H) (x y : H.val) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y)) := by
  have ht := (representative_interval H hH).2.2.2
  have hf := (FixedObjectModel.weakEquivalences_iff _).mp ht (label H x) (label H y)
  have hw := (congrArg (fun k : hom H (label H x) (label H y) ⟶ 𝟙_ SSet.{u} =>
    SSet.realizationWeakEquivalences k) (CodiscreteTerminal.toTerminal_homMap H _ _)).mp hf
  exact (CodiscreteEnrichment.toUnit_weak_iff (originalHomIso H x y).hom
    (SSet.realizationWeakEquivalences.of_isIso _)).mpr hw

/-- Each SAME full original representative point inclusion is genuinely Dwyer--Kan weak. -/
theorem point_weak (H : FixedObjects walking.{u}) (hH : representatives H) (x : walking.{u}) :
    EnrichedDwyerKan.weakEquivalences (pointMap H x) :=
  OriginalWeakUnitHomsPointRecognition.point_weak H.val (representative_hom_weak H hH) (vertex H x)

/-- The actual small A2 family retains every SAME original representative point and both original labels. -/
def generatingIntervals : MorphismProperty Carrier.{u} :=
  .ofHoms (fun p : {H : FixedObjects walking.{u} // representatives H} × walking.{u} => pointMap p.1.val p.2)

/-- The full original A2 family is genuinely small in the SAME coefficient universe. -/
instance generatingIntervals_small : generatingIntervals.{u}.IsSmall.{u} := MorphismProperty.isSmall_ofHoms _

/-- Every SAME actual original representative point inclusion belongs to the genuine small family. -/
theorem point_mem (H : FixedObjects walking.{u}) (hH : representatives H) (x : walking.{u}) :
    generatingIntervals (pointMap H x) := by
  change MorphismProperty.ofHoms
    (fun p : {H : FixedObjects walking.{u} // representatives H} × walking.{u} => pointMap p.1.val p.2) _
  exact MorphismProperty.ofHoms.mk
    (f := fun p : {H : FixedObjects walking.{u} // representatives H} × walking.{u} => pointMap p.1.val p.2)
    ((⟨H, hH⟩ : {H : FixedObjects walking.{u} // representatives H}), x)

/-- Every actual original A2 map is genuinely C0 cofibrant and Dwyer--Kan weak. -/
theorem generatingIntervals_le_cofibration_weak :
    generatingIntervals.{u} ≤ Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  rintro A B i ⟨⟨⟨H, hH⟩, x⟩⟩
  exact ⟨point_cofibration H hH x, point_weak H hH x⟩

/-- The SAME actual original A1+A2 family retains ALL positive horns and the complete original small interval family. -/
def generatingTrivialCofibrations : MorphismProperty Carrier.{u} :=
  Bergner.generatingHomHorns ⊔ generatingIntervals

/-- The full SAME original combined family is genuinely small. -/
instance generatingTrivialCofibrations_small : generatingTrivialCofibrations.{u}.IsSmall.{u} := by
  refine ⟨?_⟩
  let φ : Bergner.generatingHomHorns.{u}.toSet ⊕ generatingIntervals.{u}.toSet →
      generatingTrivialCofibrations.{u}.toSet := fun q => match q with
    | .inl h => ⟨h.val, Or.inl h.property⟩
    | .inr h => ⟨h.val, Or.inr h.property⟩
  exact small_of_surjective (f := φ) (by
    rintro ⟨q, hq | hq⟩
    · exact ⟨.inl ⟨q, hq⟩, rfl⟩
    · exact ⟨.inr ⟨q, hq⟩, rfl⟩)

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
