/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreRectifiedImagePullbackWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFibreCoverageFiniteBase
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Actual image fibres and all-component coverage of the SAME core factor

The weak ordinary pullback of the actual p over the full original Unit9 pair
is tested over the original W₀ pair. Native pullback pasting identifies each
test with the SAME p-fibre comparison at the exact Unit9 image point. Unit9's
component surjectivity and native finite-product preservation then let LeafC
transport these derived image weaknesses to every target component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal

/-- The original Segal object's actual zero pair is Kan by native Reedy
mapping-object fibrancy and its genuine degree-zero Yoneda Iso. -/
theorem originalSegalObjectPair_kan (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[0] : SSet.{u}))
  have hK := ReedyModel.innerHom_kanComplex X W (ReedyModel.isCofibrant X) hW.1
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) at hK
  let : IsFibrant ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) := hK
  let : SSet.KanComplex (W.diagram _⦋0⦌) := isFibrant_of_fibration (discreteYonedaIso W 0).inv
  let : Fibration (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌) :=
    (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
      (IsPullback.of_hasBinaryProduct' (W.diagram _⦋0⦌) (W.diagram _⦋0⦌)).flip
      ((fibration_iff (terminal.from (W.diagram _⦋0⦌))).mp inferInstance))
  exact isFibrant_of_fibration (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌)

/-- The actual SAME pair covers all target components, using the original
Unit9 component theorem twice and the native chosen product-component Iso. -/
theorem sameOriginalUnitPair_components_surjective (W : SimplicialSpace.{u}) :
    Function.Surjective (SSet.mapπ₀ (sameOriginalUnitPair W)) := by
  let A := W.diagram _⦋0⦌
  let B := (RezkCompletionData.completion.obj W).diagram _⦋0⦌
  let f : A ⟶ B := (RezkCompletionData.unit.app W).hom.app (op ⦋0⦌)
  intro q
  obtain ⟨a, ha⟩ := RezkCompletionData.unit_components_surjective W 0
      (SSet.piZeroProductEquiv B B q).1
  obtain ⟨b, hb⟩ := RezkCompletionData.unit_components_surjective W 0
      (SSet.piZeroProductEquiv B B q).2
  refine ⟨(SSet.piZeroProductEquiv A A).symm (a, b), ?_⟩
  apply (SSet.piZeroProductEquiv B B).injective
  change SSet.piZeroProductEquiv B B (SSet.mapπ₀ (prod.map f f)
    ((SSet.piZeroProductEquiv A A).symm (a, b))) = _
  rw [SSet.piZeroProductEquiv_natural, (SSet.piZeroProductEquiv A A).apply_symm_apply]
  exact Prod.ext ha hb

/-- The two full Unit9-pullback projections are the original fibration bases
over the original W₀ pair. -/
theorem sameCoreFactorUnitPairPullbackMap_over_base (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameCoreFactorUnitPairPullbackMap W hW hHat ≫
        pullback.snd (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
          (sameOriginalUnitPair W) =
      pullback.snd (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W) := by
  simp only [sameCoreFactorUnitPairPullbackMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The point test of that actual whole Unit9-pullback comparison. -/
def sameCoreFactorUnitPairPointTest (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (b : (Δ[0] : SSet.{u}) ⟶ (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) :
    pullback (pullback.snd (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W)) b ⟶
      pullback (pullback.snd
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W)) b :=
  pullback.map _ _ _ _ (sameCoreFactorUnitPairPullbackMap W hW hHat) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using
         (sameCoreFactorUnitPairPullbackMap_over_base W hW hHat).symm)
    (by simp only [Category.comp_id, Category.id_comp])

/-- Both genuine native point-pasting Isos identify this test with the SAME
p-fibre comparison at the literal original point followed by the Unit9 pair. -/
def sameCoreFactorImagePointArrowIso (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (b : (Δ[0] : SSet.{u}) ⟶ (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) :
    Arrow.mk (sameCoreFactorUnitPairPointTest W hW hHat b) ≅
      Arrow.mk (SSet.sameBasePullbackComparison (sameCoreRectification W hW hHat).p
        (sameRectifiedNativeCoreBase W hW hHat)
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
        (b ≫ sameOriginalUnitPair W)) := by
  let sourceIso := pullbackLeftPullbackSndIso
    (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W) b
  let targetIso := pullbackLeftPullbackSndIso
    (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (sameOriginalUnitPair W) b
  refine Arrow.isoMk sourceIso targetIso ?_
  change sourceIso.hom ≫
      SSet.sameBasePullbackComparison (sameCoreRectification W hW hHat).p
        (sameRectifiedNativeCoreBase W hW hHat)
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
        (b ≫ sameOriginalUnitPair W) =
    sameCoreFactorUnitPairPointTest W hW hHat b ≫ targetIso.hom
  apply pullback.hom_ext
  · simp only [sameCoreFactorUnitPairPointTest, SSet.sameBasePullbackComparison,
      sameCoreFactorUnitPairPullbackMap, sourceIso, targetIso, Category.assoc,
      pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst, pullbackLeftPullbackSndIso_hom_fst_assoc]
  · simp only [sameCoreFactorUnitPairPointTest, SSet.sameBasePullbackComparison,
      sourceIso, targetIso, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- Every actual original image-point comparison is weak, derived from the
whole Unit9-pullback map and two actual fibrations over Kan W₀×W₀. -/
theorem sameCoreFactor_imagePoint_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (b : (Δ[0] : SSet.{u}) ⟶ (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) :
    SSet.realizationWeakEquivalences
      (SSet.sameBasePullbackComparison (sameCoreRectification W hW hHat).p
        (sameRectifiedNativeCoreBase W hW hHat)
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
        (b ≫ sameOriginalUnitPair W)) := by
  let : SSet.KanComplex ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) := originalSegalObjectPair_kan W hW
  let : Fibration (sameRectifiedNativeCoreBase W hW hHat) :=
    (sameRectifiedNativeCoreBase_fibrations W hW hHat).2
  let : Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    SegalHomotopy.coreEndpoint_fibration _ hHat
  letI :
      Fibration (pullback.snd (sameRectifiedNativeCoreBase W hW hHat)
        (sameOriginalUnitPair W)) := by
    infer_instance
  let : Fibration (pullback.snd
      (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W)) := by infer_instance
  have hp := (SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (sameCoreFactorUnitPairPullbackMap W hW hHat)
    (pullback.snd (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W))
    (pullback.snd (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W)) (sameCoreFactorUnitPairPullbackMap_over_base W hW hHat)).mp
      ((weakEquivalence_iff _).mp (sameCoreFactorUnitPairPullbackMap_weak W hW hHat)) b
  apply (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (sameCoreFactorImagePointArrowIso W hW hHat b)).mp
  exact hp

/-- The actual vertex image is the SAME original point composite, not a
separately chosen target point or a replaced pair projection. -/
theorem sameCoreFactor_imageVertex_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x : ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (SSet.sameBasePullbackComparison (sameCoreRectification W hW hHat).p
        (sameRectifiedNativeCoreBase W hW hHat)
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
        (SSet.yonedaEquiv.symm ((sameOriginalUnitPair W).app (op ⦋0⦌) x))) := by
  rw [← SSet.yonedaEquiv_symm_comp]
  exact sameCoreFactor_imagePoint_weak W hW hHat (SSet.yonedaEquiv.symm x)

/-- LeafC transports the DERIVED image-pair weaknesses to all target
components. Both actual rectified fibrations are derived. -/
theorem sameCoreRectification_factor_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    SSet.realizationWeakEquivalences (sameCoreRectification W hW hHat).p := by
  let : Fibration (sameRectifiedNativeCoreBase W hW hHat) :=
    (sameRectifiedNativeCoreBase_fibrations W hW hHat).2
  let : Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    SegalHomotopy.coreEndpoint_fibration _ hHat
  exact SSet.realizationWeakEquivalence_of_image_fibres_component_coverage
    (sameOriginalUnitPair W) (sameCoreRectification W hW hHat).p
    (sameRectifiedNativeCoreBase W hW hHat)
    (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
    (sameOriginalUnitPair_components_surjective W) (sameCoreFactor_imageVertex_weak W hW hHat)

end SimplicialSpace.RezkCompletionCoreDiagonal
