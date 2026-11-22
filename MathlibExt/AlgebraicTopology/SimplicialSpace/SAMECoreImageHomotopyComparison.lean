/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalUnitCoreRelativePullback

/-!
# The actual whole-core image comparison over the SAME unit pair

Two internally derived maps from the original complete equivalence core
compare the actual core diagonal and the target core over the same Unit9 pair.
Their literal native HP square derives weakness of the HP map induced by the
actual core comparison. No weakness of that comparison or its factor is input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw

/-- The source-first/target-second native endpoint is the same original inclusion endpoint. -/
theorem coreEndpoint_eq_native (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    coreEndpoint W hW = SegalHomotopy.coreEndpoint W hW := by
  apply prod.hom_ext
  · simp only [coreEndpoint, Category.assoc, mappingEndpoint_fst,
      SegalHomotopy.coreEndpoint, prod.lift_fst, SegalHomotopy.equivalenceSource]
  · simp only [coreEndpoint, Category.assoc, mappingEndpoint_snd,
      SegalHomotopy.coreEndpoint, prod.lift_snd, SegalHomotopy.equivalenceTarget]

/-- The actual SAME comparison has the same fixed native target-core endpoint. -/
theorem sameCoreComparison_native_over_base (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameCoreComparison W hW hHat ≫
        SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat =
      sameCoreBase W hW := by
  rw [← coreEndpoint_eq_native]
  exact sameCoreComparison_over_base W hW hHat

/-- The original coefficient-zero core map followed by the actual comparison
is the whole SAME unit's core map, with the original row-one inclusion preserved. -/
theorem originalZeroCore_rowVertex_sameComparison
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (originalZeroCoreIso W hW).inv ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (corePowerDiagram W hW) ⦋0⦌ 0 ≫
          sameCoreComparison W hW hHat = sameOriginalUnitCoreMap W hW hHat := by
  let β := RezkBaselineReplacement.unit.app (rawCompletion W)
  let a : (corePowerDiagram W hW).obj (op ⦋0⦌) ⟶ coreDiagonal W hW :=
    SSet.EquifibredDiagonal.rowVertexToDiagonal (corePowerDiagram W hW) ⦋0⦌ 0
  let r : (rowPowerDiagram W (op ⦋1⦌)).obj (op ⦋0⦌) ⟶
      (rawCompletion W).diagram _⦋1⦌ :=
    SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋1⦌)) ⦋0⦌ 0
  let i0 := (corePowerInclusion W hW).app (op ⦋0⦌)
  let iW := (SegalHomotopy.equivalenceSubcomplex W hW).ι
  have ha : a ≫ coreDiagonalInclusion W hW = i0 ≫ r :=
    SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality (corePowerInclusion W hW) ⦋0⦌ 0
  have hi : (originalZeroCoreIso W hW).inv ≫ i0 =
      iW ≫ (originalZeroPowerRowIso W (op ⦋1⦌)).inv :=
    SegalHomotopy.equivalenceMap_ι (powerZeroUnitIso W).inv hW
      (powerDiagram_segal W hW (op ⦋0⦌))
  have hc : sameCoreComparison W hW hHat ≫
      (SegalHomotopy.equivalenceSubcomplex (RezkCompletionData.completion.obj W) hHat).ι =
        coreDiagonalInclusion W hW ≫ sameBetaOne W :=
    coreDiagonalComparison_ι β hW hHat
  apply (cancel_mono
    (SegalHomotopy.equivalenceSubcomplex (RezkCompletionData.completion.obj W) hHat).ι).mp
  calc
    _ = (originalZeroCoreIso W hW).inv ≫ a ≫
        (sameCoreComparison W hW hHat ≫
          (SegalHomotopy.equivalenceSubcomplex (RezkCompletionData.completion.obj W) hHat).ι) := by
      simp only [a, Category.assoc]
      rfl
    _ = (originalZeroCoreIso W hW).inv ≫ a ≫
        (coreDiagonalInclusion W hW ≫ sameBetaOne W) := by rw [hc]
    _ = ((originalZeroCoreIso W hW).inv ≫ (a ≫ coreDiagonalInclusion W hW)) ≫
        sameBetaOne W := by simp only [Category.assoc]
    _ = ((originalZeroCoreIso W hW).inv ≫ (i0 ≫ r)) ≫ sameBetaOne W := by rw [ha]
    _ = (((originalZeroCoreIso W hW).inv ≫ i0) ≫ r) ≫ sameBetaOne W := by
      simp only [Category.assoc]
    _ = ((iW ≫ (originalZeroPowerRowIso W (op ⦋1⦌)).inv) ≫ r) ≫ sameBetaOne W := by rw [hi]
    _ = iW ≫ ((originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ r) ≫ sameBetaOne W := by
      simp only [Category.assoc]
    _ = iW ≫ (rawCompletionUnit W).hom.app (op ⦋1⦌) ≫ sameBetaOne W := by
      have hr : (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ r =
          (rawCompletionUnit W).hom.app (op ⦋1⦌) :=
        originalZeroPowerRowIso_inv_rowVertex W (op ⦋1⦌)
      exact congrArg (fun f => iW ≫ f ≫ sameBetaOne W) hr
    _ = iW ≫ (RezkCompletionData.unit.app W).hom.app (op ⦋1⦌) := rfl
    _ = _ := (SegalHomotopy.equivalenceMap_ι (RezkCompletionData.unit.app W) hW hHat).symm

/-- The actual core comparison acts on the two SAME image cospans. -/
def sameCoreUnitPairComparisonCospanMap (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    cospan (sameCoreBase W hW) (sameOriginalUnitPair W) ⟶
      cospan (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W) :=
  cospanHomMk (𝟙 _) (sameCoreComparison W hW hHat) (𝟙 _)
    (by
      change sameCoreBase W hW ≫ 𝟙 _ = sameCoreComparison W hW hHat ≫
        SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat
      exact (Category.comp_id _).trans (sameCoreComparison_native_over_base W hW hHat).symm)
    (by
      change sameOriginalUnitPair W ≫ 𝟙 _ = 𝟙 _ ≫ sameOriginalUnitPair W
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The known target HP comparison is the derived whole Unit9 core-relative PB
followed by native HP comparison at the actual target endpoint fibration. -/
def sameOriginalUnitCoreTargetHomotopyComparison (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) ⟶
      (homotopyPullback (C := SSet.{u})).obj
        (cospan (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
          (sameOriginalUnitPair W)) :=
  sameOriginalUnitCoreEndpointComparison W hW hHat ≫
    (homotopyPullbackComparison (C := SSet.{u})).app _

/-- No target-core relative weakness is supplied: it follows from UnitMF14,
the actual selector-preimage restriction and the native endpoint fibration. -/
theorem sameOriginalUnitCoreTargetHomotopyComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    WeakEquivalence (sameOriginalUnitCoreTargetHomotopyComparison W hW hHat) := by
  let : WeakEquivalence (sameOriginalUnitCoreEndpointComparison W hW hHat) :=
    (weakEquivalence_iff _).mpr (sameOriginalUnitCoreEndpointComparison_weak W hW hHat)
  let : Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    SegalHomotopy.coreEndpoint_fibration _ hHat
  let : Fibration ((cospan
      (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W)).map WalkingCospan.Hom.inl) := by
    change Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    infer_instance
  let : WeakEquivalence ((homotopyPullbackComparison (C := SSet.{u})).app
      (cospan (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W))) :=
    weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _
  unfold sameOriginalUnitCoreTargetHomotopyComparison
  infer_instance

/-- The exact native HP square has BOTH original PB legs: its total leg is
the SAME unit core map and its pair leg is the original W₀ endpoint. -/
theorem originalCoreToSameUnitHP_comparison_factor
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    originalCoreToFixedSameUnitPairHomotopyPullback W hW ≫
        (homotopyPullback (C := SSet.{u})).map (sameCoreUnitPairComparisonCospanMap W hW hHat) =
      sameOriginalUnitCoreTargetHomotopyComparison W hW hHat := by
  let η := originalCoreEndpointDiagram W hW
  let a := (originalCoreZeroRawCospanIso W hW).hom ≫
    originalCoreRawToSameUnitPairCospanMap W hW ≫ sameCoreUnitPairComparisonCospanMap W hW hHat
  let lift := SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison η ⦋0⦌ 0
  have hf : (originalZeroCoreIso W hW).inv ≫ lift ≫ lim.map a =
      sameOriginalUnitCoreEndpointComparison W hW hHat := by
    apply pullback.hom_ext
    · calc
        _ = (originalZeroCoreIso W hW).inv ≫ lift ≫
            (lim.map a ≫ pullback.fst _ _) := by simp only [Category.assoc]
        _ = (originalZeroCoreIso W hW).inv ≫ lift ≫
            (pullback.fst _ _ ≫ a.app WalkingCospan.left) := by
              rw [limit.map_π a WalkingCospan.left]
        _ = (originalZeroCoreIso W hW).inv ≫ (lift ≫ pullback.fst _ _) ≫
            a.app WalkingCospan.left := by simp only [Category.assoc]
        _ = (originalZeroCoreIso W hW).inv ≫
            SSet.EquifibredDiagonal.rowVertexToDiagonal (corePowerDiagram W hW) ⦋0⦌ 0 ≫
              sameCoreComparison W hW hHat := by
          rw [(SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs η ⦋0⦌ 0).1]
          rfl
        _ = sameOriginalUnitCoreMap W hW hHat := originalZeroCore_rowVertex_sameComparison W hW hHat
        _ = sameOriginalUnitCoreEndpointComparison W hW hHat ≫ pullback.fst _ _ :=
          (sameOriginalUnitCoreEndpointComparison_legs W hW hHat).1.symm
    · calc
        _ = (originalZeroCoreIso W hW).inv ≫ lift ≫
            (lim.map a ≫ pullback.snd _ _) := by simp only [Category.assoc]
        _ = (originalZeroCoreIso W hW).inv ≫ lift ≫
            (pullback.snd _ _ ≫ a.app WalkingCospan.right) := by
              rw [limit.map_π a WalkingCospan.right]
        _ = (originalZeroCoreIso W hW).inv ≫ (lift ≫ pullback.snd _ _) ≫
            a.app WalkingCospan.right := by simp only [Category.assoc]
        _ = (originalZeroCoreIso W hW).inv ≫ η.app (op ⦋0⦌) ≫
            (originalZeroCorePairIso W).hom := by
          rw [(SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs η ⦋0⦌ 0).2]
          rfl
        _ = (originalZeroCoreIso W hW).inv ≫
            ((originalZeroCoreIso W hW).hom ≫ SegalHomotopy.coreEndpoint W hW) := by
          rw [← originalZeroCoreIso_endpoint]
        _ = SegalHomotopy.coreEndpoint W hW := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = sameOriginalUnitCoreEndpointComparison W hW hHat ≫ pullback.snd _ _ :=
          (sameOriginalUnitCoreEndpointComparison_legs W hW hHat).2.symm
  have naturality := (homotopyPullbackComparison (C := SSet.{u})).naturality a
  calc
    _ = ((originalZeroCoreIso W hW).inv ≫ lift) ≫
        ((homotopyPullbackComparison (C := SSet.{u})).app _ ≫
          (homotopyPullback (C := SSet.{u})).map a) := by
      simp only [originalCoreToFixedSameUnitPairHomotopyPullback,
          originalCoreToRawUnitHomotopyPullback,
        SSet.RezkOriginal61.kappa, Functor.mapIso_hom, a, η, lift, Functor.map_comp, Category.assoc]
      rfl
    _ = ((originalZeroCoreIso W hW).inv ≫ lift) ≫
        (lim.map a ≫ (homotopyPullbackComparison (C := SSet.{u})).app _) := by rw [← naturality]
    _ = ((originalZeroCoreIso W hW).inv ≫ lift ≫ lim.map a) ≫
        (homotopyPullbackComparison (C := SSet.{u})).app _ := by rfl
    _ = _ := by rw [hf]; rfl

/-- The actual whole-core HP comparison over the SAME unit pair is weak,
derived by two-out-of-three from the two original core-to-HP comparisons. -/
theorem sameCoreUnitPairHomotopyComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCoreUnitPairComparisonCospanMap W hW hHat)) := by
  let : WeakEquivalence (originalCoreToFixedSameUnitPairHomotopyPullback W hW) :=
    originalCoreToFixedSameUnitPairHomotopyPullback_weak W hW
  let : WeakEquivalence (sameOriginalUnitCoreTargetHomotopyComparison W hW hHat) :=
    sameOriginalUnitCoreTargetHomotopyComparison_weak W hW hHat
  let : WeakEquivalence (originalCoreToFixedSameUnitPairHomotopyPullback W hW ≫
      (homotopyPullback (C := SSet.{u})).map (sameCoreUnitPairComparisonCospanMap W hW hHat)) := by
    rw [originalCoreToSameUnitHP_comparison_factor]
    infer_instance
  exact weakEquivalence_of_precomp (originalCoreToFixedSameUnitPairHomotopyPullback W hW)
    ((homotopyPullback (C := SSet.{u})).map (sameCoreUnitPairComparisonCospanMap W hW hHat))

end SimplicialSpace.RezkCompletionCoreDiagonal
