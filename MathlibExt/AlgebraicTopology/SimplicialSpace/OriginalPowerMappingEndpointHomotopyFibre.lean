/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCoreZeroPairHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCorePowerOperatorFibreWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingFaithfulness

/-!
# The actual whole mapping-endpoint diagram of the original powers

Every row is the original outer-one mapping endpoint of the same full-J power.
The row Sharp and ALL relative-map hypotheses of Rezk 6.1 are derived internally
from actual Reedy fibrancy and the original power mapping-fibre comparisons.
The comparison remains over the same ordered coefficient-power object pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw

set_option linter.unusedVariables false in
/-- The original whole outer-one endpoint on every full-J power. -/
def originalPowerMappingEndpointDiagram (W : SimplicialSpace.{u}) :
    rowPowerDiagram W (op ⦋1⦌) ⟶ originalCorePairDiagram W where
  app n := mappingEndpoint ((powerDiagram W).obj n)
  naturality n m f := (mappingEndpoint_naturality ((powerDiagram W).map f)).symm

/-- Every original row endpoint is a fibration by the actual power's Reedy fibrancy. -/
theorem originalPowerMappingEndpointDiagram_row_fibration (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : SimplexCategory) :
    Fibration ((originalPowerMappingEndpointDiagram W).app (op n)) :=
  ReedyModel.mappingEndpoint_fibration ((powerDiagram W).obj (op n))
    (powerDiagram_segal W hW (op n)).1

/-- Genuine row fibrations give all native Sharp comparisons by right properness. -/
theorem originalPowerMappingEndpointDiagram_row_sharp (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (n : SimplexCategory) :
    SSet.SharpComparisonDraft.Sharp ((originalPowerMappingEndpointDiagram W).app (op n)) := by
  let : Fibration ((originalPowerMappingEndpointDiagram W).app (op n)) :=
    originalPowerMappingEndpointDiagram_row_fibration W hW n
  intro T t
  let : Fibration ((cospan ((originalPowerMappingEndpointDiagram W).app (op n)) t).map
      WalkingCospan.Hom.inl) := originalPowerMappingEndpointDiagram_row_fibration W hW n
  exact weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
    (cospan ((originalPowerMappingEndpointDiagram W).app (op n)) t)

/-- The ALL-operator relative map is the native original mapping-endpoint comparison. -/
theorem originalPowerMappingEndpointDiagram_relativeComparison (W : SimplicialSpace.{u})
    {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.EquifibredDiagonal.relativeComparison (originalPowerMappingEndpointDiagram W) f =
      mappingEndpointComparison ((powerDiagram W).map f.op) :=
  rfl

/-- Its weakness is derived from the actual full mapping-fibre family of that
operator and the native Reedy-fibrant endpoint criterion; no relative WE is supplied. -/
theorem originalPowerMappingEndpointDiagram_relativeComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {n m : SimplexCategory} (f : n ⟶ m) :
    WeakEquivalence (SSet.EquifibredDiagonal.relativeComparison
      (originalPowerMappingEndpointDiagram W) f) := by
  rw [weakEquivalence_iff, originalPowerMappingEndpointDiagram_relativeComparison]
  exact (mappingEndpointComparison_realizationWeak_iff ((powerDiagram W).map f.op)
    (powerDiagram_segal W hW (op m)).1 (powerDiagram_segal W hW (op n)).1).mpr
      (RezkCorePowerFibres.originalPowerOperator_mappingFibre_weak W hW f.op)

/-- Rezk's Theorem 6.1 gives diagonal sharpness for this whole mapping diagram.
The project corollary supplies all native homotopy pullback comparisons;
both hypothesis families are derived above. -/
theorem originalPowerMappingEndpointDiagram_all_simplex_and_homotopy_pullback
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.SharpSaturation.allSimplexComparisons
        (SSet.simplicialDiagonalFunctor.map (originalPowerMappingEndpointDiagram W)) ∧
      SSet.SharpComparisonDraft.Sharp
        (SSet.simplicialDiagonalFunctor.map (originalPowerMappingEndpointDiagram W)) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)),
        WeakEquivalence (SSet.RezkOriginal61.kappa (originalPowerMappingEndpointDiagram W) n v) :=
  SSet.RezkOriginal61.all_simplex_sharp_and_native_homotopy_pullback
    (originalPowerMappingEndpointDiagram W) (originalPowerMappingEndpointDiagram_row_sharp W hW)
    (originalPowerMappingEndpointDiagram_relativeComparison_weak W hW)

/-- The pair-diagonal Iso retains the original Raw(W) mapping endpoint with both faces. -/
theorem originalPowerMappingEndpointDiagram_diagonal_pair (W : SimplicialSpace.{u}) :
    SSet.simplicialDiagonalFunctor.map (originalPowerMappingEndpointDiagram W) ≫
        (originalCorePairDiagonalIso W).hom = mappingEndpoint (rawCompletion W) := by
  apply prod.hom_ext
  · rw [Category.assoc, (originalCorePairDiagonalIso_legs W).1]
    let d : rowPowerDiagram W (op ⦋1⦌) ⟶ rowPowerDiagram W (op ⦋0⦌) :=
      SimplicialObject.δ ((powerDiagram W ⋙ forget).flip) (1 : Fin 2)
    have hd : SSet.simplicialDiagonalFunctor.map d =
        (rawCompletion W).diagram.δ (1 : Fin 2) := by rfl
    have hf : originalPowerMappingEndpointDiagram W ≫ originalCorePairFst W = d := by
      apply NatTrans.ext
      funext n
      change mappingEndpoint ((powerDiagram W).obj n) ≫ prod.fst =
        ((powerDiagram W).obj n).diagram.δ (1 : Fin 2)
      exact mappingEndpoint_fst ((powerDiagram W).obj n)
    have hc := (SSet.simplicialDiagonalFunctor.map_comp (originalPowerMappingEndpointDiagram W)
      (originalCorePairFst W)).symm
    refine hc.trans ((congrArg SSet.simplicialDiagonalFunctor.map hf).trans ?_)
    rw [hd]
    exact (mappingEndpoint_fst (rawCompletion W)).symm
  · rw [Category.assoc, (originalCorePairDiagonalIso_legs W).2.1]
    let d : rowPowerDiagram W (op ⦋1⦌) ⟶ rowPowerDiagram W (op ⦋0⦌) :=
      SimplicialObject.δ ((powerDiagram W ⋙ forget).flip) (0 : Fin 2)
    have hd : SSet.simplicialDiagonalFunctor.map d =
        (rawCompletion W).diagram.δ (0 : Fin 2) := by rfl
    have hf : originalPowerMappingEndpointDiagram W ≫ originalCorePairSnd W = d := by
      apply NatTrans.ext
      funext n
      change mappingEndpoint ((powerDiagram W).obj n) ≫ prod.snd =
        ((powerDiagram W).obj n).diagram.δ (0 : Fin 2)
      exact mappingEndpoint_snd ((powerDiagram W).obj n)
    have hc := (SSet.simplicialDiagonalFunctor.map_comp (originalPowerMappingEndpointDiagram W)
      (originalCorePairSnd W)).symm
    refine hc.trans ((congrArg SSet.simplicialDiagonalFunctor.map hf).trans ?_)
    rw [hd]
    exact (mappingEndpoint_snd (rawCompletion W)).symm

/-- The exact native kappa is the original whole PB lift before HP comparison. -/
theorem originalPowerMappingEndpointDiagram_kappa_actual_lift
    (W : SimplicialSpace.{u}) (n : SimplexCategory) (v : Fin (n.len + 1)) :
    SSet.RezkOriginal61.kappa (originalPowerMappingEndpointDiagram W) n v =
      pullback.lift (SSet.EquifibredDiagonal.rowVertexToDiagonal
          (rowPowerDiagram W (op ⦋1⦌)) n v)
        ((originalPowerMappingEndpointDiagram W).app (op n))
        (SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality
          (originalPowerMappingEndpointDiagram W) n v) ≫
        (homotopyPullbackComparison (C := SSet.{u})).app
          (cospan (SSet.simplicialDiagonalFunctor.map (originalPowerMappingEndpointDiagram W))
            (SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) n v)) :=
  SSet.RezkOriginal61.kappa_actual_original_lift (originalPowerMappingEndpointDiagram W) n v

end SimplicialSpace.RezkCompletionCoreDiagonal
