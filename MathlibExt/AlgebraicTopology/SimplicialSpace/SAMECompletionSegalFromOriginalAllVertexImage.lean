/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Segalness of the original completion from all-vertex unit comparisons.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalUnitAllVertexHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalChosenSpineVertexFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFibreCoverageFiniteBase

/-!
# Segalness of the original SAME completion, derived from W and its Segal proof

Both source and target higher Unit fibre maps are the literal original maps.
Source Segal trivial fibrations, the derived Unit mapping-fibre weaknesses and
the newly derived higher Unit fibre weaknesses give the target comparisons at
every original Unit image tuple. The actual all-vertex and chosen-spine vertex
projections are fibrations. Original Unit component surjectivity, finite
component products and LeafC extend those image tests to all target tuples.
No target Segalness, full Unit weakness or completeness is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace.RezkCompletionAllVertex
open RezkCompletionCoreDiagonal OriginalAllVertexComparison
open FixedTupleSpinePrefix OriginalChosenSpineFixedTupleBaseChange

/-- Original Unit9 component surjectivity covers every full finite tuple, including k=0 and k=1. -/
theorem sameOriginalUnitTuple_components_surjective (W : SimplicialSpace.{u}) (k : ℕ) :
    Function.Surjective (SSet.mapπ₀ (sameOriginalUnitTuple W k)) :=
  SSet.mapPiZero_surjective_finite_Pi_map (k + 1)
    (fun _ : Fin (k + 1) => (RezkCompletionData.unit.app W).hom.app (op ⦋0⦌))
    (fun _ => RezkCompletionData.unit_components_surjective W 0)

/-- The target direct comparison is weak at each actual original Unit image tuple.
This uses target RF alone; target Segalness is the conclusion still being derived. -/
theorem sameCompletion_directComparison_at_original_image_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    WeakEquivalence (simplexAllVertexComparisonDirect (RezkCompletionData.completion.obj W)
      k hk (fun i => mappingVertexMap (RezkCompletionData.unit.app W) (x i))) := by
  let unit : W ⟶ RezkCompletionData.completion.obj W := RezkCompletionData.unit.app W
  let : WeakEquivalence (simplexAllVertexComparisonDirect W k hk x) :=
    ((mem_trivialFibrations_iff _).mp
      (simplexAllVertexComparisonDirect_trivialFibration W k hk hW x)).2
  let : WeakEquivalence (chosenSpineTupleFibreMap unit k hk x) :=
    OriginalTupleMappingFibreWeakness.chosenSpineTupleMap_weak unit hW.1
      (RezkCompletionData.completion_fibrant W) k hk x
      (fun i => sameOriginalUnit_mappingFibre_weak W hW (x i.castSucc) (x i.succ))
  let : WeakEquivalence (simplexAllVertexFibreMap unit k x) :=
    (weakEquivalence_iff _).mpr (sameOriginalUnit_simplexAllVertexFibreMap_weak W hW k hk x)
  let : WeakEquivalence (simplexAllVertexFibreMap unit k x ≫
      simplexAllVertexComparisonDirect (RezkCompletionData.completion.obj W) k hk
        (fun i => mappingVertexMap unit (x i))) := by
    rw [← simplexAllVertexComparisonDirect_naturality unit k hk x]
    infer_instance
  exact weakEquivalence_of_precomp (simplexAllVertexFibreMap unit k x)
    (simplexAllVertexComparisonDirect (RezkCompletionData.completion.obj W) k hk
      (fun i => mappingVertexMap unit (x i)))

/-- The original direct chosen-spine comparison is the native same-base point comparison,
with both actual simplex/Delta0 pullback projections retained. -/
theorem simplexAllVertexComparisonDirect_sameBase (V : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (k + 1) → (V.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexComparisonDirect V k hk x =
      SSet.sameBasePullbackComparison (segalStrictComparison V k hk)
        (simplexAllVertexMap V k) (chosenSpineVertexMap V k hk)
        (strictComparison_allVertex V k hk) (tuplePoint V k x) := by
  apply pullback.hom_ext
  · rw [(simplexAllVertexComparisonDirect_legs V k hk x).1]
    simp only [SSet.sameBasePullbackComparison, pullback.map, pullback.lift_fst]
  · rw [(simplexAllVertexComparisonDirect_legs V k hk x).2]
    simp only [SSet.sameBasePullbackComparison, pullback.map, pullback.lift_snd, Category.comp_id]

/-- Each actual vertex of the full original tuple gives exactly its Unit image point test. -/
theorem sameCompletion_original_imagePoint_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k)
    (a : (tupleVertexBase W k) _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (SSet.sameBasePullbackComparison
        (segalStrictComparison (RezkCompletionData.completion.obj W) k hk)
        (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
        (chosenSpineVertexMap (RezkCompletionData.completion.obj W) k hk)
        (strictComparison_allVertex (RezkCompletionData.completion.obj W) k hk)
        (SSet.yonedaEquiv.symm ((sameOriginalUnitTuple W k).app (op ⦋0⦌) a))) := by
  let point := SSet.yonedaEquiv.symm a
  let x := tupleVerticesOfPoint W k point
  have point_eq : tuplePoint W k x = point := tuplePoint_tupleVerticesOfPoint W k point
  have moved : tuplePoint (RezkCompletionData.completion.obj W) k
      (fun i => mappingVertexMap (RezkCompletionData.unit.app W) (x i)) =
        SSet.yonedaEquiv.symm ((sameOriginalUnitTuple W k).app (op ⦋0⦌) a) := by
    calc
      _ = tuplePoint W k x ≫ sameOriginalUnitTuple W k :=
        (originalTuplePoint_naturality (RezkCompletionData.unit.app W) k x).symm
      _ = point ≫ sameOriginalUnitTuple W k := by rw [point_eq]
      _ = _ := by simp only [point, SSet.yonedaEquiv_symm_comp]
  rw [← moved, ← simplexAllVertexComparisonDirect_sameBase]
  exact (weakEquivalence_iff _).mp
      (sameCompletion_directComparison_at_original_image_weak W hW k hk x)

/-- The target's literal chosen Segal comparison is weak in every original k≥2.
All projection fibrations and image coverage are derived here. -/
theorem sameCompletion_segalStrictComparison_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k) :
    SSet.realizationWeakEquivalences
      (segalStrictComparison (RezkCompletionData.completion.obj W) k hk) := by
  let target := RezkCompletionData.completion.obj W
  let : Fibration (simplexAllVertexMap target k) :=
    OriginalAllVertexReedy.allVertexMap_fibration target k (RezkCompletionData.completion_fibrant W)
  let : Fibration (chosenSpineVertexMap target k hk) :=
    OriginalChosenSpineFibration.chosenSpineVertexMap_fibration target k hk
      (RezkCompletionData.completion_fibrant W)
  exact SSet.realizationWeakEquivalence_of_image_fibres_component_coverage
    (sameOriginalUnitTuple W k) (segalStrictComparison target k hk)
    (simplexAllVertexMap target k) (chosenSpineVertexMap target k hk)
    (strictComparison_allVertex target k hk)
    (sameOriginalUnitTuple_components_surjective W k)
    (sameCompletion_original_imagePoint_weak W hW k hk)

/-- The original SAME completion is Segal from W and its original Segal proof alone. -/
theorem sameCompletion_segal (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    segalSpaces (RezkCompletionData.completion.obj W) := by
  apply (segalSpaces_iff _).mpr
  refine ⟨RezkCompletionData.completion_fibrant W, ?_⟩
  intro k hk
  exact (segalStrictComparison_weak_iff (RezkCompletionData.completion.obj W) k hk).mp
    (sameCompletion_segalStrictComparison_weak W hW k hk)

end SimplicialSpace.RezkCompletionAllVertex
