/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalUnitMappingHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalEquivalenceFibreWeakComparison
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The actual SAME-unit comparison on the complete equivalence core

The full Unit9 mapping-fibre weakness is invoked from its derived original
power-diagram proof. Intrinsic reflection identifies the actual component
preimage, and the existing native restriction theorem gives every complete
equivalence-fibre map. The caller supplies only original Segalness and the
independently derived target Segalness, with no unit-FF/core/complete outcome.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open SegalHomotopy

/-- The SAME unit acts on the whole original equivalence subcomplex. -/
def sameOriginalUnitCoreMap (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (equivalenceSubcomplex W hW : SSet.{u}) ⟶
      (equivalenceSubcomplex (RezkCompletionData.completion.obj W) hHat : SSet.{u}) :=
  equivalenceMap (RezkCompletionData.unit.app W) hW hHat

/-- Source d₁ and target d₀ give the exact original SAME-unit endpoint square. -/
theorem sameOriginalUnitCoreMap_endpoint (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameOriginalUnitCoreMap W hW hHat ≫
        SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat =
      SegalHomotopy.coreEndpoint W hW ≫ sameOriginalUnitPair W := by
  apply prod.hom_ext
  · simp only [sameOriginalUnitCoreMap, SegalHomotopy.coreEndpoint, sameOriginalUnitPair,
      Category.assoc, prod.lift_fst, prod.lift_fst_assoc, prod.map_fst]
    exact equivalenceSource_naturality (RezkCompletionData.unit.app W) hW hHat
  · simp only [sameOriginalUnitCoreMap, SegalHomotopy.coreEndpoint, sameOriginalUnitPair,
      Category.assoc, prod.lift_snd, prod.lift_snd_assoc, prod.map_snd]
    exact equivalenceTarget_naturality (RezkCompletionData.unit.app W) hW hHat

/-- The original complete core maps to the native target-core pullback over
the original W₀ pair, without assuming this comparison is a fibration. -/
def sameOriginalUnitCoreEndpointComparison (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (equivalenceSubcomplex W hW : SSet.{u}) ⟶
      pullback (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W) :=
  pullback.lift (sameOriginalUnitCoreMap W hW hHat) (SegalHomotopy.coreEndpoint W hW)
    (sameOriginalUnitCoreMap_endpoint W hW hHat)

/-- Both complete original core and ordered-pair projections remain literal. -/
theorem sameOriginalUnitCoreEndpointComparison_legs
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameOriginalUnitCoreEndpointComparison W hW hHat ≫ pullback.fst _ _ =
        sameOriginalUnitCoreMap W hW hHat ∧
      sameOriginalUnitCoreEndpointComparison W hW hHat ≫ pullback.snd _ _ =
        SegalHomotopy.coreEndpoint W hW :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- Native pasting and actual Unit9 point naturality identify the target
point fibre with the complete equivalence fibre at the two actual images. -/
def sameOriginalUnitCorePointTargetIso
    (W : SimplicialSpace.{u})
    (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback (pullback.snd
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W)) (mappingPointPair W x y) ≅
      equivalenceFibre (RezkCompletionData.completion.obj W) hHat
        (mappingVertexMap (RezkCompletionData.unit.app W) x)
        (mappingVertexMap (RezkCompletionData.unit.app W) y) :=
  pullbackLeftPullbackSndIso _ _ (mappingPointPair W x y) ≪≫
    pullback.congrHom rfl (mappingPointPair_naturality (RezkCompletionData.unit.app W) x y)

/-- The same chosen point map of the actual unit-core endpoint comparison. -/
def sameOriginalUnitCorePointMap
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    equivalenceFibre W hW x y ⟶
      pullback (pullback.snd
        (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W)) (mappingPointPair W x y) :=
  pullback.map _ _ _ _ (sameOriginalUnitCoreEndpointComparison W hW hHat) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using
         (sameOriginalUnitCoreEndpointComparison_legs W hW hHat).2.symm)
    (by simp only [Category.comp_id, Category.id_comp])

private theorem congrPullback_fst {A B C : SSet.{u}}
    {f₁ f₂ : A ⟶ C} {g₁ g₂ : B ⟶ C} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem congrPullback_snd {A B C : SSet.{u}}
    {f₁ f₂ : A ⟶ C} {g₁ g₂ : B ⟶ C} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem pointTarget_fst (W : SimplicialSpace.{u})
    (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (sameOriginalUnitCorePointTargetIso W hHat x y).hom ≫
      pullback.fst (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (mappingPointPair (RezkCompletionData.completion.obj W)
          (mappingVertexMap (RezkCompletionData.unit.app W) x)
          (mappingVertexMap (RezkCompletionData.unit.app W) y)) =
      pullback.fst _ (mappingPointPair W x y) ≫
        pullback.fst (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
          (sameOriginalUnitPair W) := by
  let e := pullbackLeftPullbackSndIso
    (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (sameOriginalUnitPair W) (mappingPointPair W x y)
  have h := congrPullback_fst
    (f₁ := SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
    (mappingPointPair_naturality (RezkCompletionData.unit.app W) x y)
  exact (Category.assoc e.hom _ _).trans
    ((congrArg (fun f => e.hom ≫ f) h).trans
      (pullbackLeftPullbackSndIso_hom_fst _ _ _))

private theorem pointTarget_snd (W : SimplicialSpace.{u})
    (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (sameOriginalUnitCorePointTargetIso W hHat x y).hom ≫
      pullback.snd (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (mappingPointPair (RezkCompletionData.completion.obj W)
          (mappingVertexMap (RezkCompletionData.unit.app W) x)
          (mappingVertexMap (RezkCompletionData.unit.app W) y)) =
      pullback.snd _ (mappingPointPair W x y) := by
  let e := pullbackLeftPullbackSndIso
    (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (sameOriginalUnitPair W) (mappingPointPair W x y)
  have h := congrPullback_snd
    (f₁ := SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) rfl
    (mappingPointPair_naturality (RezkCompletionData.unit.app W) x y)
  exact (Category.assoc e.hom _ _).trans
    ((congrArg (fun f => e.hom ≫ f) h).trans
      (pullbackLeftPullbackSndIso_hom_snd _ _ _))

/-- Both native point-pullback projections recover the actual complete
equivalence-fibre map of the original SAME unit. -/
theorem sameOriginalUnitCorePointMap_comp_targetIso
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    sameOriginalUnitCorePointMap W hW hHat x y ≫
        (sameOriginalUnitCorePointTargetIso W hHat x y).hom =
      equivalenceFibreMap (RezkCompletionData.unit.app W) hW hHat
        (x := x) (y := y) rfl rfl := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pointTarget_fst, sameOriginalUnitCorePointMap,
      pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
      Category.comp_id,
      sameOriginalUnitCoreEndpointComparison,
      sameOriginalUnitCoreMap, equivalenceFibreMap]
    rfl
  · simp only [Category.assoc, pointTarget_snd, sameOriginalUnitCorePointMap,
      pullback.map, pullback.lift_snd,
      Category.comp_id,
      equivalenceFibreMap]
    rfl

/-- Full Unit9 MF weakness derives the exact original core-point weakness;
the native selector-preimage theorem performs intrinsic reflection internally. -/
theorem sameOriginalUnitCorePointMap_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W))
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (sameOriginalUnitCorePointMap W hW hHat x y) := by
  have he := equivalenceFibreMap_weak_of_mappingFibreWeak
    (RezkCompletionData.unit.app W) hW hHat (sameOriginalUnit_mappingFibre_weak W hW) x y
  have hiso : SSet.realizationWeakEquivalences
      (sameOriginalUnitCorePointTargetIso W hHat x y).hom :=
    SSet.realizationWeakEquivalences.of_isIso _
  apply (SSet.realizationWeakEquivalences.postcomp_iff _
    (sameOriginalUnitCorePointTargetIso W hHat x y).hom hiso).mp
  rwa [sameOriginalUnitCorePointMap_comp_targetIso]

/-- The actual complete unit-core relative PB is weak over the original
Kan W₀ pair. That Kan fact is derived from original Reedy fibrancy, not RawW. -/
theorem sameOriginalUnitCoreEndpointComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    SSet.realizationWeakEquivalences (sameOriginalUnitCoreEndpointComparison W hW hHat) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[0] : SSet.{u}))
  have hK := ReedyModel.innerHom_kanComplex X W (ReedyModel.isCofibrant X) hW.1
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) at hK
  let : IsFibrant ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) := hK
  let : SSet.KanComplex (W.diagram _⦋0⦌) := isFibrant_of_fibration (discreteYonedaIso W 0).inv
  let : SSet.KanComplex ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) := by
    let : Fibration (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌) :=
      (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
        (IsPullback.of_hasBinaryProduct' (W.diagram _⦋0⦌) (W.diagram _⦋0⦌)).flip
        ((fibration_iff (terminal.from (W.diagram _⦋0⦌))).mp inferInstance))
    exact isFibrant_of_fibration (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌)
  let : Fibration (SegalHomotopy.coreEndpoint W hW) := SegalHomotopy.coreEndpoint_fibration W hW
  let : Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    SegalHomotopy.coreEndpoint_fibration _ hHat
  let : Fibration (pullback.snd
      (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W)) := by infer_instance
  apply (SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (sameOriginalUnitCoreEndpointComparison W hW hHat) (SegalHomotopy.coreEndpoint W hW)
    (pullback.snd (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W)) (sameOriginalUnitCoreEndpointComparison_legs W hW hHat).2).mpr
  intro b
  let x := (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌).app (op ⦋0⦌)
    (SSet.yonedaEquiv b)
  let y := (prod.snd : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌).app (op ⦋0⦌)
    (SSet.yonedaEquiv b)
  have hb : mappingPointPair W x y = b := by
    apply prod.hom_ext
    · rw [mappingPointPair_fst]
      simpa only [x, Equiv.symm_apply_apply] using
        (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv b)
          (prod.fst : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌)).symm
    · rw [mappingPointPair_snd]
      simpa only [y, Equiv.symm_apply_apply] using
        (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv b)
          (prod.snd : (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶ W.diagram _⦋0⦌)).symm
  rw [← hb]
  exact sameOriginalUnitCorePointMap_weak W hW hHat x y

end SimplicialSpace.RezkCompletionCoreDiagonal
