/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalPowerMappingEndpointHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCoreFixedSameUnitPairHomotopyFibre

/-!
# Original SAME-unit mapping-fibre weakness from the actual power diagram

The actual Rezk 6.1 mapping kappa is transported through Raw20's zero-power
and pair-diagonal Isos, followed by the genuine baseline beta on row one and
both object factors. The target mapping endpoint is a fibration because the
SAME baseline replacement is Reedy fibrant. No unit-FF, target Segalness,
Raw-base Kan, global core weakness or completeness outcome is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SSet.modelCategoryQuillen.modelCategory

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw

/-- The actual zero-power mapping endpoint square retains both ordered faces. -/
theorem originalZeroMappingIso_endpoint (W : SimplicialSpace.{u}) :
    (originalZeroPowerRowIso W (op ⦋1⦌)).hom ≫ mappingEndpoint W =
      (originalPowerMappingEndpointDiagram W).app (op ⦋0⦌) ≫
        (originalZeroCorePairIso W).hom := by
  change ((powerZeroUnitIso W).hom.hom.app (op ⦋1⦌)) ≫ mappingEndpoint W =
    mappingEndpoint ((powerDiagram W).obj (op ⦋0⦌)) ≫
      prod.map ((powerZeroUnitIso W).hom.hom.app (op ⦋0⦌))
        ((powerZeroUnitIso W).hom.hom.app (op ⦋0⦌))
  exact (mappingEndpoint_naturality (powerZeroUnitIso W).hom).symm

/-- The native cospan Iso identifies the actual mapping kappa's base with
the original raw unit pair, leaving the whole Raw(W)₁ source unchanged. -/
def originalMappingZeroRawCospanIso (W : SimplicialSpace.{u}) :
    cospan (SSet.simplicialDiagonalFunctor.map (originalPowerMappingEndpointDiagram W))
        (SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) ⦋0⦌ 0) ≅
      cospan (mappingEndpoint (rawCompletion W)) (originalRawUnitPair W) :=
  cospanIsoMk (originalCorePairDiagonalIso W) (Iso.refl _) (originalZeroCorePairIso W)
    (by
      change SSet.simplicialDiagonalFunctor.map (originalPowerMappingEndpointDiagram W) ≫
        (originalCorePairDiagonalIso W).hom =
          𝟙 ((rawCompletion W).diagram _⦋1⦌) ≫ mappingEndpoint (rawCompletion W)
      simpa only [Category.id_comp] using originalPowerMappingEndpointDiagram_diagonal_pair W)
    (originalCorePair_rowZero_rawUnit W)

/-- The whole original W₁ maps to the HP along its original raw unit pair. -/
def originalMappingToRawUnitHomotopyPullback (W : SimplicialSpace.{u}) :
    W.diagram _⦋1⦌ ⟶ (homotopyPullback (C := SSet.{u})).obj
      (cospan (mappingEndpoint (rawCompletion W)) (originalRawUnitPair W)) :=
  (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫
    SSet.RezkOriginal61.kappa (originalPowerMappingEndpointDiagram W) ⦋0⦌ 0 ≫
      ((homotopyPullback (C := SSet.{u})).mapIso (originalMappingZeroRawCospanIso W)).hom

/-- Its weakness uses the two genuine Isos and the internally derived mapping kappa. -/
theorem originalMappingToRawUnitHomotopyPullback_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    WeakEquivalence (originalMappingToRawUnitHomotopyPullback W) := by
  let : WeakEquivalence
      (SSet.RezkOriginal61.kappa (originalPowerMappingEndpointDiagram W) ⦋0⦌ 0) :=
    (originalPowerMappingEndpointDiagram_all_simplex_and_homotopy_pullback W hW).2.2 ⦋0⦌ 0
  unfold originalMappingToRawUnitHomotopyPullback
  infer_instance

/-- The fixed baseline beta on the actual original raw mapping row. -/
def sameBetaOne (W : SimplicialSpace.{u}) :
    (rawCompletion W).diagram _⦋1⦌ ⟶ (RezkCompletionData.completion.obj W).diagram _⦋1⦌ :=
  (RezkBaselineReplacement.unit.app (rawCompletion W)).hom.app (op ⦋1⦌)

/-- This row-one beta is weak by the actual baseline component theorem. -/
theorem sameBetaOne_weak (W : SimplicialSpace.{u}) : WeakEquivalence (sameBetaOne W) :=
  (weakEquivalence_iff _).mpr (RezkBaselineReplacement.unit_components (rawCompletion W) 1).2

/-- Native beta naturality retains the original mapping endpoint square. -/
theorem sameBetaOne_mappingEndpoint (W : SimplicialSpace.{u}) :
    mappingEndpoint (rawCompletion W) ≫ sameBaselineBetaPair W =
      sameBetaOne W ≫ mappingEndpoint (RezkCompletionData.completion.obj W) :=
  mappingEndpoint_naturality (RezkBaselineReplacement.unit.app (rawCompletion W))

/-- The raw mapping cospan maps to the SAME target mapping cospan with beta₁,
beta₀ on BOTH factors, and the unchanged original W₀ pair. -/
def originalMappingRawToSameUnitPairCospanMap (W : SimplicialSpace.{u}) :
    cospan (mappingEndpoint (rawCompletion W)) (originalRawUnitPair W) ⟶
      cospan (mappingEndpoint (RezkCompletionData.completion.obj W)) (sameOriginalUnitPair W) :=
  cospanHomMk (sameBaselineBetaPair W) (sameBetaOne W)
    (𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)))
    (sameBetaOne_mappingEndpoint W)
    (by
      change originalRawUnitPair W ≫ sameBaselineBetaPair W =
        𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) ≫ sameOriginalUnitPair W
      simpa only [Category.id_comp] using originalRawUnitPair_betaPair W)

/-- All three actual component weaknesses are derived baseline facts or identity. -/
theorem originalMappingRawToSameUnitPairHomotopyMap_weak (W : SimplicialSpace.{u}) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (originalMappingRawToSameUnitPairCospanMap W)) := by
  apply homotopyPullback_map_weakEquivalence
  intro j
  cases j with
  | none => exact sameBaselineBetaPair_weak W
  | some pair =>
      cases pair with
      | left => exact sameBetaOne_weak W
      | right => exact inferInstanceAs
          (WeakEquivalence (𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌))))

/-- The actual W₁-to-HP comparison over the SAME unit pair. -/
def originalMappingToFixedSameUnitPairHomotopyPullback (W : SimplicialSpace.{u}) :
    W.diagram _⦋1⦌ ⟶ (homotopyPullback (C := SSet.{u})).obj
      (cospan (mappingEndpoint (RezkCompletionData.completion.obj W)) (sameOriginalUnitPair W)) :=
  originalMappingToRawUnitHomotopyPullback W ≫
    (homotopyPullback (C := SSet.{u})).map (originalMappingRawToSameUnitPairCospanMap W)

/-- The original diagram and beta₁/beta² derive this full HP weakness. -/
theorem originalMappingToFixedSameUnitPairHomotopyPullback_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    WeakEquivalence (originalMappingToFixedSameUnitPairHomotopyPullback W) := by
  let : WeakEquivalence (originalMappingToRawUnitHomotopyPullback W) :=
    originalMappingToRawUnitHomotopyPullback_weak W hW
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (originalMappingRawToSameUnitPairCospanMap W)) :=
    originalMappingRawToSameUnitPairHomotopyMap_weak W
  unfold originalMappingToFixedSameUnitPairHomotopyPullback
  infer_instance

/-- The full native HP composite is the literal SAME-unit mapping-endpoint
PB lift followed by the target's native HP comparison. -/
theorem originalMappingToFixedSameUnitPairHomotopyPullback_factor
    (W : SimplicialSpace.{u}) :
    originalMappingToFixedSameUnitPairHomotopyPullback W =
      mappingEndpointComparison (RezkCompletionData.unit.app W) ≫
        (homotopyPullbackComparison (C := SSet.{u})).app
          (cospan (mappingEndpoint (RezkCompletionData.completion.obj W))
              (sameOriginalUnitPair W)) := by
  let η := originalPowerMappingEndpointDiagram W
  let a := (originalMappingZeroRawCospanIso W).hom ≫
    originalMappingRawToSameUnitPairCospanMap W
  let lift := SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison η ⦋0⦌ 0
  have hfirst : (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift ≫ lim.map a =
      mappingEndpointComparison (RezkCompletionData.unit.app W) := by
    apply pullback.hom_ext
    · calc
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift ≫
            (lim.map a ≫ pullback.fst _ _) := by simp only [Category.assoc]
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift ≫
            (pullback.fst _ _ ≫ a.app WalkingCospan.left) := by
          rw [limit.map_π a WalkingCospan.left]
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫
            (lift ≫ pullback.fst _ _) ≫ a.app WalkingCospan.left := by
          simp only [Category.assoc]
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫
            SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋1⦌)) ⦋0⦌ 0 ≫
              sameBetaOne W := by
          rw [(SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs η ⦋0⦌ 0).1]
          rfl
        _ = (rawCompletionUnit W).hom.app (op ⦋1⦌) ≫ sameBetaOne W := by
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun q => q ≫ sameBetaOne W)
              (originalZeroPowerRowIso_inv_rowVertex W (op ⦋1⦌)))
        _ = (RezkCompletionData.unit.app W).hom.app (op ⦋1⦌) := rfl
        _ = mappingEndpointComparison (RezkCompletionData.unit.app W) ≫
            pullback.fst _ _ := (mappingEndpointComparison_fst _).symm
    · calc
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift ≫
            (lim.map a ≫ pullback.snd _ _) := by simp only [Category.assoc]
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift ≫
            (pullback.snd _ _ ≫ a.app WalkingCospan.right) := by
          rw [limit.map_π a WalkingCospan.right]
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫
            (lift ≫ pullback.snd _ _) ≫ a.app WalkingCospan.right := by
          simp only [Category.assoc]
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫
            (originalPowerMappingEndpointDiagram W).app (op ⦋0⦌) ≫
              (originalZeroCorePairIso W).hom := by
          rw [(SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs η ⦋0⦌ 0).2]
          rfl
        _ = (originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫
            ((originalZeroPowerRowIso W (op ⦋1⦌)).hom ≫ mappingEndpoint W) := by
          rw [← originalZeroMappingIso_endpoint]
        _ = mappingEndpoint W := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = mappingEndpointComparison (RezkCompletionData.unit.app W) ≫
            pullback.snd _ _ := (mappingEndpointComparison_snd _).symm
  have naturality := (homotopyPullbackComparison (C := SSet.{u})).naturality a
  calc
    originalMappingToFixedSameUnitPairHomotopyPullback W =
        ((originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift) ≫
          ((homotopyPullbackComparison (C := SSet.{u})).app _ ≫
            (homotopyPullback (C := SSet.{u})).map a) := by
      simp only [originalMappingToFixedSameUnitPairHomotopyPullback,
        originalMappingToRawUnitHomotopyPullback, SSet.RezkOriginal61.kappa,
        SSet.SharpComparisonDraft.comparison, Functor.mapIso_hom, a, η, lift,
        Functor.map_comp, Category.assoc]
    _ = ((originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift) ≫
        (lim.map a ≫ (homotopyPullbackComparison (C := SSet.{u})).app _) := by
      rw [← naturality]
    _ = ((originalZeroPowerRowIso W (op ⦋1⦌)).inv ≫ lift ≫ lim.map a) ≫
        (homotopyPullbackComparison (C := SSet.{u})).app _ := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun q => q ≫ (homotopyPullbackComparison (C := SSet.{u})).app
      (cospan (mappingEndpoint (RezkCompletionData.completion.obj W))
        (sameOriginalUnitPair W))) hfirst

/-- The actual SAME-unit relative mapping PB is weak; target fibrancy is
derived from the same baseline construction, with no target Segal premise. -/
theorem sameOriginalUnit_mappingEndpointComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    WeakEquivalence (mappingEndpointComparison (RezkCompletionData.unit.app W)) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : Fibration (mappingEndpoint (RezkCompletionData.completion.obj W)) :=
    ReedyModel.mappingEndpoint_fibration (RezkCompletionData.completion.obj W)
      (RezkCompletionData.completion_fibrant W)
  let comparison := (homotopyPullbackComparison (C := SSet.{u})).app
    (cospan (mappingEndpoint (RezkCompletionData.completion.obj W)) (sameOriginalUnitPair W))
  let : Fibration ((cospan (mappingEndpoint (RezkCompletionData.completion.obj W))
      (sameOriginalUnitPair W)).map WalkingCospan.Hom.inl) := by
    change Fibration (mappingEndpoint (RezkCompletionData.completion.obj W))
    infer_instance
  have hcomparison : WeakEquivalence comparison :=
    weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _
  have htotal : WeakEquivalence (mappingEndpointComparison (RezkCompletionData.unit.app W) ≫
      comparison) := by
    rw [← originalMappingToFixedSameUnitPairHomotopyPullback_factor]
    exact originalMappingToFixedSameUnitPairHomotopyPullback_weak W hW
  exact weakEquivalence_of_postcomp (mappingEndpointComparison (RezkCompletionData.unit.app W))
    comparison (hg := hcomparison) (hfg := htotal)

/-- Every original SAME-unit mapping-fibre map is weak, derived internally
from the full native endpoint PB criterion and actual baseline fibrancy. -/
theorem sameOriginalUnit_mappingFibre_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingFibre.map (RezkCompletionData.unit.app W)
      (x := x) (y := y) rfl rfl) := by
  let : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  exact (mappingEndpointComparison_realizationWeak_iff (RezkCompletionData.unit.app W)
    hW.1 (RezkCompletionData.completion_fibrant W)).mp
      ((weakEquivalence_iff _).mp (sameOriginalUnit_mappingEndpointComparison_weak W hW)) x y

end SimplicialSpace.RezkCompletionCoreDiagonal
