/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableInterval

/-!
# Exact original forward and reverse coefficients of the genuine countable interval

The unchanged full native factors recover the supplied original free-arrow
map. Its actual whole forward Hom therefore retains the original supplied
equivalence coefficient through every original projection. Degree-zero
nonemptiness gives an actual reverse vertex in the SAME full interval.
No desired coefficient or weak interval is supplied as an outcome input.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
open FixedObjects OriginalWalkingArrowFreeSingleHomIso
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf C e))

/-- The SAME whole forward Hom equality retains both actual original countable-piece maps. -/
theorem forward_hom_factor :
    homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
    homMap (toLocalization a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) =
    homMap (OriginalEquivalenceLocalization.fromFree a e he)
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) :=
  (homMap_comp (fromFree a e he) (toLocalization a e he) _ _).symm.trans
    (congrArg (fun f => homMap f (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u}))) (free_toLocalization a e he))

/-- The SAME complete original generator coefficient survives the actual countable union and every original projection.
-/
theorem generator_original :
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (toLocalization a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (OriginalEquivalenceLocalization.toResolved a e he)
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a))
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a)
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) =
      (SSet.unitHomEquiv _).symm e := by
  have h := forward_hom_factor a e he
  have h' := congrArg (fun k =>
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫ k ≫
    homMap (OriginalEquivalenceLocalization.toResolved a e he)
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
    homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a))
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
    ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a)
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u}))) h
  simpa only [Category.assoc] using h'.trans (OriginalEquivalenceLocalization.generator_original a e he)

/-- The actual whole full reverse Hom contains a real original degree-zero vertex. -/
def reverseVertex :
    (hom (fixedObject a e he) (BergnerTwoObject.target (𝟙_ SSet.{u}))
      (BergnerTwoObject.source (𝟙_ SSet.{u}))) _⦋0⦌ :=
  Classical.choice (hom_zero_nonempty a e he _ _)

/-- Both SAME actual original interval labels remain distinct before their possibly coincident original target images.
-/
theorem original_labels_distinct :
    vertex (fixedObject a e he) (BergnerTwoObject.source (𝟙_ SSet.{u})) ≠
      vertex (fixedObject a e he) (BergnerTwoObject.target (𝟙_ SSet.{u})) := by
  intro h
  have hl := (verticesEquiv (fixedObject a e he)).injective h
  have hu := congrArg ULift.down hl
  exact (by decide : SSet.WalkingHom.source (X := 𝟙_ SSet.{u}) ≠ SSet.WalkingHom.target) hu

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
