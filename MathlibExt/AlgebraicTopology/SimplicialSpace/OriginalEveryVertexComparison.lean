/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Fixed-tuple base change of the chosen spine-vertex comparison.
-- Uses the original tuple-spine constructions imported below.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalTupleSpineAllArity
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Segal comparisons with prescribed vertices

The simplex fibre with all vertices prescribed compares naturally to the corresponding chosen-
spine fibre, preserving every vertex and both pullback projections. Explicit pullback-pasting
isomorphisms identify the direct and transported comparisons; for a Reedy-fibrant Segal space in
dimension at least two, both comparison arrows are trivial Kan fibrations.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
open SimplicialSpace SimplicialSpace.FixedTupleSpinePrefix
namespace SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

/-- The internally chosen nested pullback retains the actual simplex and fixed tuple. -/
def nestedSimplexTupleFibre (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (segalStrictComparison W k hk)
    (pullback.fst (chosenSpineVertexMap W k hk) (tuplePoint W k x))

/-- The comparison is the actual second projection, with no supplied lifting/weak output. -/
def nestedSimplexTupleComparison (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    nestedSimplexTupleFibre W k hk x ⟶ chosenSpineTupleFibre W k hk x :=
  pullback.snd _ _

/-- Original RF+Segal internally yields the trivial fibration of this SAME comparison. -/
theorem nestedSimplexTupleComparison_trivialFibration (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) (hW : segalSpaces W)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (nestedSimplexTupleComparison W k hk x) := by
  exact (trivialFibrations SSet.{u}).of_isPullback
    (IsPullback.of_hasPullback (segalStrictComparison W k hk)
      (pullback.fst (chosenSpineVertexMap W k hk) (tuplePoint W k x)))
    (segalStrictComparison_trivialFibration W k hk hW)

/-- The native whole pasting Iso reaches the actual fibre of the composite vertex map. -/
def nestedSimplexTuplePastingIso (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    nestedSimplexTupleFibre W k hk x ≅
      pullback (segalStrictComparison W k hk ≫ chosenSpineVertexMap W k hk)
        (tuplePoint W k x) :=
  pullbackRightPullbackFstIso (chosenSpineVertexMap W k hk)
    (tuplePoint W k x) (segalStrictComparison W k hk)

/-- The first actual simplex projection remains unchanged by the whole pasting Iso. -/
theorem nestedSimplexTuplePastingIso_hom_fst (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    (nestedSimplexTuplePastingIso W k hk x).hom ≫ pullback.fst _ _ =
      pullback.fst (segalStrictComparison W k hk)
        (pullback.fst (chosenSpineVertexMap W k hk) (tuplePoint W k x)) :=
  pullbackRightPullbackFstIso_hom_fst _ _ _

/-- The terminal Delta0 leg is the SAME nested point projection. -/
theorem nestedSimplexTuplePastingIso_hom_snd (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    (nestedSimplexTuplePastingIso W k hk x).hom ≫ pullback.snd _ _ =
      nestedSimplexTupleComparison W k hk x ≫
        pullback.snd (chosenSpineVertexMap W k hk) (tuplePoint W k x) :=
  pullbackRightPullbackFstIso_hom_snd _ _ _

end SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

namespace SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

private theorem firstSourceConstant (k : ℕ) (hk : 2 ≤ k) :
    SimplexCategory.δ (1 : Fin 2) ≫
      SimplexCategory.mkOfSucc (⟨0, by omega⟩ : Fin k) =
    SimplexCategory.const ⦋0⦌ ⦋k⦌ (0 : Fin (k + 1)) := by
  ext j
  fin_cases j
  rfl

private theorem successorTargetConstant (k : ℕ) (i : Fin k) :
    SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfSucc i =
      SimplexCategory.const ⦋0⦌ ⦋k⦌ i.succ := by
  ext j
  fin_cases j
  rfl

/-- EVERY original standard-simplex vertex, without a chosen edge at zero. -/
def simplexAllVertexMap (W : SimplicialSpace.{u}) (k : ℕ) :
    W.diagram _⦋k⦌ ⟶ tupleVertexBase W k :=
  Pi.lift (fun i => W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op)

/-- Actual consecutive-edge endpoints give the exact complete all-vertex square. -/
theorem strictComparison_allVertex (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k) :
    segalStrictComparison W k hk ≫ chosenSpineVertexMap W k hk =
      simplexAllVertexMap W k := by
  have edge (i : Fin k) :
      segalStrictComparison W k hk ≫
        ((fullPrefixChosenIso W k hk).inv ≫ edgeProjection W k k le_rfl i) =
      W.diagram.map (SimplexCategory.mkOfSucc i).op := by
    rw [fullPrefixChosenIso_edge, segalStrictComparison_edge]
  apply Pi.hom_ext
  intro i
  simp only [chosenSpineVertexMap, tupleVertexMap, simplexAllVertexMap,
    Category.assoc, Pi.lift_comp_π]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [vertexProjection, Fin.cases_zero]
    calc
      segalStrictComparison W k hk ≫
          ((fullPrefixChosenIso W k hk).inv ≫
            (edgeProjection W k k le_rfl ⟨0, by omega⟩ ≫ W.diagram.δ (1 : Fin 2))) =
          W.diagram.map (SimplexCategory.mkOfSucc (⟨0, by omega⟩ : Fin k)).op ≫
            W.diagram.δ (1 : Fin 2) := by
        simpa only [Category.assoc] using
          congrArg (fun a => a ≫ W.diagram.δ (1 : Fin 2)) (edge ⟨0, by omega⟩)
      _ = W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ (0 : Fin (k + 1))).op := by
        change W.diagram.map (SimplexCategory.mkOfSucc (⟨0, by omega⟩ : Fin k)).op ≫
          W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op = _
        rw [← W.diagram.map_comp, ← op_comp, firstSourceConstant k hk]
  · simp only [vertexProjection, Fin.cases_succ]
    calc
      segalStrictComparison W k hk ≫
          ((fullPrefixChosenIso W k hk).inv ≫
            (edgeProjection W k k le_rfl j ≫ W.diagram.δ (0 : Fin 2))) =
          W.diagram.map (SimplexCategory.mkOfSucc j).op ≫ W.diagram.δ (0 : Fin 2) := by
        simpa only [Category.assoc] using
          congrArg (fun a => a ≫ W.diagram.δ (0 : Fin 2)) (edge j)
      _ = W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ j.succ).op := by
        change W.diagram.map (SimplexCategory.mkOfSucc j).op ≫
          W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op = _
        rw [← W.diagram.map_comp, ← op_comp, successorTargetConstant]

/-- The literal fibre of every original simplex vertex over its SAME tuple. -/
abbrev simplexAllVertexFibre (W : SimplicialSpace.{u}) (k : ℕ)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (simplexAllVertexMap W k) (tuplePoint W k x)

/-- The internally proved all-vertex identity supplies the actual whole pasting Iso. -/
def nestedToSimplexAllVertexIso (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    nestedSimplexTupleFibre W k hk x ≅ simplexAllVertexFibre W k x :=
  nestedSimplexTuplePastingIso W k hk x ≪≫
    pullback.congrHom (strictComparison_allVertex W k hk)
        (rfl : tuplePoint W k x = tuplePoint W k x)

/-- The simplex-to-tuple comparison uses the actual inverse and SAME nested projection. -/
def simplexAllVertexComparison (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexFibre W k x ⟶ chosenSpineTupleFibre W k hk x :=
  (nestedToSimplexAllVertexIso W k hk x).inv ≫ nestedSimplexTupleComparison W k hk x

/-- Original RF+Segal proves the actual comparison TF; no comparison/IsPullback outcome input. -/
theorem simplexAllVertexComparison_trivialFibration (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) (hW : segalSpaces W)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (simplexAllVertexComparison W k hk x) := by
  exact ((trivialFibrations SSet.{u}).cancel_left_of_respectsIso
    (nestedToSimplexAllVertexIso W k hk x).inv
    (nestedSimplexTupleComparison W k hk x)).mpr
      (nestedSimplexTupleComparison_trivialFibration W k hk hW x)

end SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

namespace SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

/-- Every original tuple-base coordinate moves through the same zero-level space map. -/
def originalTupleBaseMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) (k : ℕ) :
    tupleVertexBase W k ⟶ tupleVertexBase V k :=
  CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) => f.hom.app (Opposite.op ⦋0⦌))

/-- The original all-vertex arrow commutes with the actual source and target space maps. -/
theorem simplexAllVertexMap_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) (k : ℕ) :
    f.hom.app (Opposite.op ⦋k⦌) ≫ simplexAllVertexMap V k =
      simplexAllVertexMap W k ≫ originalTupleBaseMap f k := by
  apply Pi.hom_ext
  intro i
  simpa only [simplexAllVertexMap, originalTupleBaseMap, Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc, CategoryTheory.Limits.Pi.map_π] using
    (f.hom.naturality (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op).symm

/-- The same Delta0 tuple point carries ALL original vertices, with no private helper reuse. -/
theorem originalTuplePoint_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePoint W k x ≫ originalTupleBaseMap f k =
      tuplePoint V k (fun i => mappingVertexMap f (x i)) := by
  apply Pi.hom_ext
  intro i
  simp only [originalTupleBaseMap, Category.assoc, CategoryTheory.Limits.Pi.map_π, tuplePoint,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc, SSet.yonedaEquiv_symm_comp, mappingVertexMap]

/-- The literal all-vertex fibre map is constructed through both native pullback legs. -/
def simplexAllVertexFibreMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexFibre W k x ⟶
      simplexAllVertexFibre V k (fun i => mappingVertexMap f (x i)) :=
  pullback.lift (pullback.fst _ _ ≫ f.hom.app (Opposite.op ⦋k⦌)) (pullback.snd _ _)
    (by rw [Category.assoc, simplexAllVertexMap_naturality, ← Category.assoc,
      pullback.condition, Category.assoc, originalTuplePoint_naturality])

/-- Both actual fibre projections retain the original space map and unchanged Delta0 source. -/
theorem simplexAllVertexFibreMap_legs {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexFibreMap f k x ≫
      pullback.fst (simplexAllVertexMap V k) (tuplePoint V k (fun i => mappingVertexMap f (x i))) =
        pullback.fst (simplexAllVertexMap W k) (tuplePoint W k x) ≫ f.hom.app (Opposite.op ⦋k⦌) ∧
    simplexAllVertexFibreMap f k x ≫
      pullback.snd (simplexAllVertexMap V k) (tuplePoint V k (fun i => mappingVertexMap f (x i))) =
        pullback.snd (simplexAllVertexMap W k) (tuplePoint W k x) := by
  constructor <;> simp only [simplexAllVertexFibreMap, pullback.lift_fst, pullback.lift_snd]

/-- The direct simplex-to-chosen-spine comparison is the SAME universal pullback lift. -/
def simplexAllVertexComparisonDirect (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexFibre W k x ⟶ chosenSpineTupleFibre W k hk x :=
  (IsPullback.of_hasPullback (chosenSpineVertexMap W k hk) (tuplePoint W k x)).lift
    (pullback.fst _ _ ≫ segalStrictComparison W k hk) (pullback.snd _ _)
    (by rw [Category.assoc, strictComparison_allVertex]; exact pullback.condition)

/-- Pullback cancellation internally identifies the direct comparison as the actual TF base
change. -/
theorem simplexAllVertexComparisonDirect_trivialFibration (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) (hW : segalSpaces W)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    trivialFibrations SSet.{u} (simplexAllVertexComparisonDirect W k hk x) := by
  have outer : IsPullback
      (pullback.fst (simplexAllVertexMap W k) (tuplePoint W k x))
      (pullback.snd (simplexAllVertexMap W k) (tuplePoint W k x))
      (segalStrictComparison W k hk ≫ chosenSpineVertexMap W k hk) (tuplePoint W k x) := by
    rw [strictComparison_allVertex]
    exact IsPullback.of_hasPullback _ _
  have base := IsPullback.of_bot' outer
    (IsPullback.of_hasPullback (chosenSpineVertexMap W k hk) (tuplePoint W k x))
  exact (trivialFibrations SSet.{u}).of_isPullback base
    (segalStrictComparison_trivialFibration W k hk hW)

end SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

namespace SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

/-- BOTH legs of the direct comparison are its actual native pullback lift components. -/
theorem simplexAllVertexComparisonDirect_legs (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexComparisonDirect W k hk x ≫
      pullback.fst (chosenSpineVertexMap W k hk) (tuplePoint W k x) =
        pullback.fst (simplexAllVertexMap W k) (tuplePoint W k x) ≫
          segalStrictComparison W k hk ∧
    simplexAllVertexComparisonDirect W k hk x ≫
      pullback.snd (chosenSpineVertexMap W k hk) (tuplePoint W k x) =
        pullback.snd (simplexAllVertexMap W k) (tuplePoint W k x) := by
  constructor <;> simp only [simplexAllVertexComparisonDirect,
    IsPullback.lift_fst, IsPullback.lift_snd]

/-- The full comparison square retains the actual source/target map and every fixed vertex. -/
theorem simplexAllVertexComparisonDirect_naturality {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexComparisonDirect W k hk x ≫ chosenSpineTupleFibreMap f k hk x =
      simplexAllVertexFibreMap f k x ≫
        simplexAllVertexComparisonDirect V k hk (fun i => mappingVertexMap f (x i)) := by
  apply pullback.hom_ext
  · calc
      (simplexAllVertexComparisonDirect W k hk x ≫ chosenSpineTupleFibreMap f k hk x) ≫
          pullback.fst (chosenSpineVertexMap V k hk)
            (tuplePoint V k (fun i => mappingVertexMap f (x i))) =
          (pullback.fst (simplexAllVertexMap W k) (tuplePoint W k x) ≫
            segalStrictComparison W k hk) ≫ lim.map (segalMappingCospanMap f k hk) := by
        rw [Category.assoc, (chosenSpineTupleFibreMap_legs f k hk x).1,
          ← Category.assoc, (simplexAllVertexComparisonDirect_legs W k hk x).1]
      _ = (pullback.fst (simplexAllVertexMap W k) (tuplePoint W k x) ≫
          f.hom.app (Opposite.op ⦋k⦌)) ≫ segalStrictComparison V k hk := by
        rw [Category.assoc, ← segalStrictComparison_naturality, ← Category.assoc]
      _ = (simplexAllVertexFibreMap f k x ≫
          simplexAllVertexComparisonDirect V k hk (fun i => mappingVertexMap f (x i))) ≫
          pullback.fst (chosenSpineVertexMap V k hk)
            (tuplePoint V k (fun i => mappingVertexMap f (x i))) := by
        symm
        rw [Category.assoc, (simplexAllVertexComparisonDirect_legs V k hk _).1,
          ← Category.assoc, (simplexAllVertexFibreMap_legs f k x).1]
  · calc
      (simplexAllVertexComparisonDirect W k hk x ≫ chosenSpineTupleFibreMap f k hk x) ≫
          pullback.snd (chosenSpineVertexMap V k hk)
            (tuplePoint V k (fun i => mappingVertexMap f (x i))) =
          pullback.snd (simplexAllVertexMap W k) (tuplePoint W k x) := by
        rw [Category.assoc, (chosenSpineTupleFibreMap_legs f k hk x).2,
          (simplexAllVertexComparisonDirect_legs W k hk x).2]
      _ = (simplexAllVertexFibreMap f k x ≫
          simplexAllVertexComparisonDirect V k hk (fun i => mappingVertexMap f (x i))) ≫
          pullback.snd (chosenSpineVertexMap V k hk)
            (tuplePoint V k (fun i => mappingVertexMap f (x i))) := by
        rw [Category.assoc, (simplexAllVertexComparisonDirect_legs V k hk _).2,
          (simplexAllVertexFibreMap_legs f k x).2]

end SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

namespace SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange

/-- Native congrHom preserves BOTH original transported simplex and Delta0 projections. -/
theorem simplexAllVertexComparison_transport_legs (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexComparison W k hk x ≫
      pullback.fst (chosenSpineVertexMap W k hk) (tuplePoint W k x) =
        pullback.fst (simplexAllVertexMap W k) (tuplePoint W k x) ≫
          segalStrictComparison W k hk ∧
    simplexAllVertexComparison W k hk x ≫
      pullback.snd (chosenSpineVertexMap W k hk) (tuplePoint W k x) =
        pullback.snd (simplexAllVertexMap W k) (tuplePoint W k x) := by
  constructor
  · dsimp only [simplexAllVertexComparison, nestedToSimplexAllVertexIso,
      nestedSimplexTupleComparison, nestedSimplexTuplePastingIso,
      nestedSimplexTupleFibre, simplexAllVertexFibre, chosenSpineTupleFibre]
    simp only [Iso.trans_inv, Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst,
      pullback.congrHom_inv, pullback.map, pullback.lift_fst_assoc,
      Category.comp_id]
  · dsimp only [simplexAllVertexComparison, nestedToSimplexAllVertexIso,
      nestedSimplexTupleComparison, nestedSimplexTuplePastingIso,
      nestedSimplexTupleFibre, simplexAllVertexFibre, chosenSpineTupleFibre]
    simp only [Iso.trans_inv, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd,
      pullback.congrHom_inv, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The direct lift and whole-pasting transport are the SAME arrow through their actual two legs. -/
theorem simplexAllVertexComparisonDirect_eq_transport (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexComparisonDirect W k hk x = simplexAllVertexComparison W k hk x := by
  apply pullback.hom_ext
  · exact (simplexAllVertexComparisonDirect_legs W k hk x).1.trans
      (simplexAllVertexComparison_transport_legs W k hk x).1.symm
  · exact (simplexAllVertexComparisonDirect_legs W k hk x).2.trans
      (simplexAllVertexComparison_transport_legs W k hk x).2.symm

end SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange
