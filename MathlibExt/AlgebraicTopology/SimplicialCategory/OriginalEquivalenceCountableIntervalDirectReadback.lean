/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReindexedProjectionReadback

/-!
# Direct full original coefficient readback from the actual countable interval

The unchanged countable-piece projection, core resolution and actual
fixed-core inclusion form the genuine original fixed-label factor. Its
full projection is the SAME original functor into C. Reading the original
free generator through this actual whole factor recovers exactly the
supplied equivalence, with only its proved endpoint transports.
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

/-- The SAME actual full fixed-label factor through every retained original countable-piece and core projection. -/
def fixedProjection : fixedObject a e he ⟶ OriginalEquivalenceTwoLabelReindexing.fixedTarget a :=
  toLocalization a e he ≫ OriginalEquivalenceLocalization.toResolved a e he ≫
    ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a) ≫
    ComponentEquivalenceCore.fixedInclusion (OriginalEquivalenceTwoLabelReindexing.object a)

/-- The entire original factor Hom is exactly the SAME complete native projection coefficient chain. -/
theorem fixedProjection_hom (x y : walking.{u}) :
    homMap (fixedProjection a e he) x y =
      homMap (toLocalization a e he) x y ≫
        homMap (OriginalEquivalenceLocalization.toResolved a e he) x y ≫
        homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a)) x y ≫
        ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a) x y := by
  let L := toLocalization a e he
  let R := OriginalEquivalenceLocalization.toResolved a e he
  let Q := ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a)
  let I := ComponentEquivalenceCore.fixedInclusion (OriginalEquivalenceTwoLabelReindexing.object a)
  exact (homMap_comp L (R ≫ Q ≫ I) x y).trans
    ((congrArg (fun k => homMap L x y ≫ k) (homMap_comp R (Q ≫ I) x y)).trans
      ((congrArg (fun k => homMap L x y ≫ homMap R x y ≫ k) (homMap_comp Q I x y)).trans
        (congrArg (fun k => homMap L x y ≫ homMap R x y ≫ homMap Q x y ≫ k)
          (ComponentEquivalenceCore.fixedInclusion_hom (OriginalEquivalenceTwoLabelReindexing.object a) x y))))

/-- The SAME full actual original projection recovers the supplied generator after the genuine fixed-label factor. -/
theorem fixed_generator_original :
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (fixedProjection a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) = (SSet.unitHomEquiv _).symm e := by
  rw [fixedProjection_hom]
  exact generator_original a e he

/-- The genuine original projected factor is the SAME existing original interval functor, including all Hom maps. -/
theorem fixedProjection_toOriginal :
    EnrichedFunctor.comp SSet.{u} (fixedProjection a e he).val
      (OriginalEquivalenceTwoLabelReindexing.projection a) = toOriginal a e he := rfl

/-- The entire original Hom map into C is the SAME fixed-label coefficient with exactly its proved original endpoint
equalities. -/
theorem toOriginal_hom (x y : walking.{u}) :
    (toOriginal a e he).map (vertex (fixedObject a e he) x) (vertex (fixedObject a e he) y) ≫
      eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t)
        (toOriginal_obj a e he x) (toOriginal_obj a e he y)) =
      homMap (fixedProjection a e he) x y := by
  exact OriginalEquivalenceTwoLabelReindexing.projected_hom a (fixedProjection a e he) x y

/-- The SAME actual original interval forward unit retains exactly the supplied equivalence after its full original Hom
projection. -/
theorem direct_generator_original :
    (FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u}))) ≫
      ((toOriginal a e he).map
        (vertex (fixedObject a e he) (BergnerTwoObject.source (𝟙_ SSet.{u})))
        (vertex (fixedObject a e he) (BergnerTwoObject.target (𝟙_ SSet.{u}))) ≫
        eqToHom (congrArg₂ (fun s t : C => s ⟶[SSet.{u}] t)
          (toOriginal_obj a e he (BergnerTwoObject.source (𝟙_ SSet.{u})))
          (toOriginal_obj a e he (BergnerTwoObject.target (𝟙_ SSet.{u}))))) =
      (SSet.unitHomEquiv _).symm e := by
  exact (congrArg (fun k =>
    (FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u}))) ≫ k)
    (toOriginal_hom a e he (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})))).trans
      ((Category.assoc _ _ _).trans (fixed_generator_original a e he))

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceCountableInterval
