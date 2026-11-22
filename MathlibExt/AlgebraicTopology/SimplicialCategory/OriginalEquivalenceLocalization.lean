/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceTwoLabelReindexing
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWalkingLocalizationHoms

/-!
# The actual original equivalence factors through a full weak localization pullback

The supplied original equivalence vertex is retained on two actual
labels, with an independent target-object universe and coincident
images allowed. Its genuine core resolution and SAME native completion
unit construct the actual localization pullback. Every full Hom maps
weakly to the original unit. Its two full projections and original
forward coefficient recover the SAME supplied original arrow.

The separate countable fixed-cofibrant A2 interval extraction is not an
input or conclusion here.
-/

noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceLocalization
open FixedObjects ScalarGroupoidCompletion OriginalWalkingArrowFreeSingleHomIso
open OriginalEquivalenceTwoLabelReindexing
variable {C : Type v} [EnrichedCategory SSet.{u} C] (a : walking.{u} → C)
variable (e : (a (BergnerTwoObject.source (𝟙_ SSet.{u})) ⟶[SSet.{u}]
  a (BergnerTwoObject.target (𝟙_ SSet.{u}))) _⦋0⦌)
variable (he : IsIso (ComponentCategory.arrowOf C e))

/-- The SAME full original free-arrow lift into the genuine original two-label core resolution. -/
abbrev resolvedArrow : free.{u} ⟶ resolvedFixedObject a := toResolution a e he

/-- The actual original localization pullback, retaining the SAME full native unit and horn right factor. -/
abbrev fixedObject : FixedObjects walking.{u} :=
  OriginalCompletionLocalizationLift.object (resolvedArrow a e he)

/-- The full original varying-object pullback carrier retains its SAME two actual labels. -/
abbrev object : Carrier.{u} := (fixedObject a e he).val

/-- The actual full original free-arrow map into that SAME localization pullback. -/
abbrev fromFree : free.{u} ⟶ fixedObject a e he :=
  OriginalCompletionLocalizationLift.lift (resolvedArrow a e he)

/-- The genuine whole original first projection to the unchanged original core resolution. -/
abbrev toResolved : fixedObject a e he ⟶ resolvedFixedObject a :=
  OriginalCompletionLocalizationPullback.toSource (resolvedFixedObject a)
    (fixedMap (resolvedArrow a e he))

/-- The actual two whole original factors recover the SAME original resolved arrow. -/
theorem free_toResolved : fromFree a e he ≫ toResolved a e he = resolvedArrow a e he :=
  OriginalCompletionLocalizationLift.lift_toSource (resolvedArrow a e he)

/-- Every actual full original localization Hom is genuinely weak to the SAME scalar unit. -/
theorem hom_toUnit_weak (x y : walking.{u}) :
    SSet.realizationWeakEquivalences
      (CodiscreteEnrichment.toUnit (FixedObjects.hom (fixedObject a e he) x y)) := by
  let _ : ModelCategory (FixedObjects walking.{u}) := FixedObjectModel.modelCategory walking
  let _ : IsCofibrant (resolvedFixedObject a) :=
    ComponentEquivalenceCore.resolved_cofibrant (OriginalEquivalenceTwoLabelReindexing.object a)
  exact OriginalWalkingLocalizationHoms.pullbackHom_toUnit_weak (resolvedArrow a e he) x y

/-- The SAME whole original projection through its core inclusion retains an independent original target universe. -/
def toOriginal : EnrichedFunctor SSet.{u} (object a e he) C :=
  EnrichedFunctor.comp SSet.{u} (toResolved a e he).val
    (EnrichedFunctor.comp SSet.{u}
      (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a)).val
      (EnrichedFunctor.comp SSet.{u}
        (ComponentEquivalenceCore.inclusion (OriginalEquivalenceTwoLabelReindexing.object a))
        (OriginalEquivalenceTwoLabelReindexing.projection a)))

/-- Every actual original vertex retains exactly its original supplied image object. -/
theorem toOriginal_obj (x : walking.{u}) :
    (toOriginal a e he).obj (vertex (fixedObject a e he) x) = a x := by
  change a ((ComponentEquivalenceCore.resolutionRight
    (OriginalEquivalenceTwoLabelReindexing.object a)).val.obj
      ((toResolved a e he).val.obj (vertex (fixedObject a e he) x))) = a x
  have h₁ := map_vertex (toResolved a e he) x
  have h₂ := map_vertex (ComponentEquivalenceCore.resolutionRight
    (OriginalEquivalenceTwoLabelReindexing.object a)) x
  exact (congrArg (fun z => a ((ComponentEquivalenceCore.resolutionRight
    (OriginalEquivalenceTwoLabelReindexing.object a)).val.obj z)) h₁).trans
      (congrArg a h₂)

/-- The full original generator recovers the SAME supplied forward coefficient through both actual projections. -/
theorem generator_original :
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
      homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (toResolved a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a))
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a)
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) =
      (SSet.unitHomEquiv _).symm e := by
  have hp := congrArg (fun f =>
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫
    homMap f (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
    homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a))
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
    ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a)
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})))
      (free_toResolved a e he)
  have hc := homMap_comp (fromFree a e he) (toResolved a e he)
    (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u}))
  have hcoef := congrArg (fun m =>
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫ m ≫
    homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a))
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
    ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a)
      (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u}))) hc
  have hg := OriginalEquivalenceTwoLabelReindexing.generator_original a e he
  have ha := congrArg (fun m =>
    FreeSingleHom.generator (BergnerTwoObject.source (𝟙_ SSet.{u}))
      (BergnerTwoObject.target (𝟙_ SSet.{u})) (𝟙_ SSet.{u}) ≫ m)
    (Category.assoc
      (homMap (fromFree a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})))
      (homMap (toResolved a e he) (BergnerTwoObject.source (𝟙_ SSet.{u}))
        (BergnerTwoObject.target (𝟙_ SSet.{u})))
      (homMap (ComponentEquivalenceCore.resolutionRight (OriginalEquivalenceTwoLabelReindexing.object a))
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u})) ≫
      ComponentEquivalenceCore.inclusionHom (OriginalEquivalenceTwoLabelReindexing.object a)
        (BergnerTwoObject.source (𝟙_ SSet.{u})) (BergnerTwoObject.target (𝟙_ SSet.{u}))))
  exact ha.symm.trans (hcoef.symm.trans (hp.trans hg))

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceLocalization
