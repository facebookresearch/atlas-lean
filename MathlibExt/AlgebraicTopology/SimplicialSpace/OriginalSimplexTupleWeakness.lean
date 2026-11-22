/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original simplex-tuple fibre comparisons from the tuple-spine and vertex constructions.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalEveryVertexComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalTupleSpineAllArity
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFiniteKanProductWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibre

/-!
# Weak maps on simplex and spine tuple fibres

For maps between Reedy fibrant simplicial spaces, weakness on each adjacent mapping fibre
implies weakness on the chosen-spine tuple fibre in arities at least two. If both spaces are
Segal, the same hypotheses give a realization weak equivalence on the corresponding all-vertex
simplex fibre.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory
open SimplicialSpace SimplicialSpace.FixedTupleSpinePrefix
open SimplicialSpace.OriginalChosenSpineFixedTupleBaseChange
namespace SimplicialSpace.OriginalTupleMappingFibreWeakness

/-- All original adjacent MF weak maps give the SAME higher chosen-spine fibre weak map. -/
theorem chosenSpineTupleMap_weak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : IsFibrant W) (hV : IsFibrant V)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌)
    (hMF : ∀ i : Fin k, SSet.realizationWeakEquivalences
      (mappingFibre.map f (x := x i.castSucc) (y := x i.succ) rfl rfl)) :
    WeakEquivalence (chosenSpineTupleFibreMap f k hk x) := by
  let a := fun i : Fin k => mappingFibre.map f
    (x := x i.castSucc) (y := x i.succ) rfl rfl
  let A : Fin k → SSet.{u} := fun i => mappingFibre W (x i.castSucc) (x i.succ)
  let B : Fin k → SSet.{u} := fun i => mappingFibre V
    (mappingVertexMap f (x i.castSucc)) (mappingVertexMap f (x i.succ))
  let : ∀ i : Fin k, SSet.KanComplex (A i) := fun i =>
    ReedyModel.mappingFibre_kanComplex W (x i.castSucc) (x i.succ) hW
  let : ∀ i : Fin k, SSet.KanComplex (B i) := fun i =>
    ReedyModel.mappingFibre_kanComplex V
      (mappingVertexMap f (x i.castSucc)) (mappingVertexMap f (x i.succ)) hV
  have productWeak : SSet.realizationWeakEquivalences (CategoryTheory.Limits.Pi.map a) :=
    SSet.OriginalFiniteKanProducts.realizationWeakEquivalence_finPiMap k A B a hMF
  let : WeakEquivalence (CategoryTheory.Limits.Pi.map a) :=
    (weakEquivalence_iff _).mpr productWeak
  have fac : chosenSpineTupleFibreMap f k hk x =
      (chosenSpineTupleFibreIso W k hk x).hom ≫ CategoryTheory.Limits.Pi.map a ≫
      (chosenSpineTupleFibreIso V k hk (fun i => mappingVertexMap f (x i))).inv := by
    rw [← Category.assoc,
        ← chosenSpineTupleFibreIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [fac]
  infer_instance

/-- Original RF+Segal at both objects and all MF weaknesses give the actual all-vertex simplex
map. -/
theorem simplexAllVertexFibreMap_weak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V)
    (k : ℕ) (hk : 2 ≤ k) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌)
    (hMF : ∀ i : Fin k, SSet.realizationWeakEquivalences
      (mappingFibre.map f (x := x i.castSucc) (y := x i.succ) rfl rfl)) :
    SSet.realizationWeakEquivalences (simplexAllVertexFibreMap f k x) := by
  let : WeakEquivalence (simplexAllVertexComparisonDirect W k hk x) :=
    ((mem_trivialFibrations_iff _).mp
      (simplexAllVertexComparisonDirect_trivialFibration W k hk hW x)).2
  let : WeakEquivalence (simplexAllVertexComparisonDirect V k hk
      (fun i => mappingVertexMap f (x i))) :=
    ((mem_trivialFibrations_iff _).mp
      (simplexAllVertexComparisonDirect_trivialFibration V k hk hV _)).2
  let : WeakEquivalence (chosenSpineTupleFibreMap f k hk x) :=
    chosenSpineTupleMap_weak f ((segalSpaces_iff W).mp hW).1
      ((segalSpaces_iff V).mp hV).1 k hk x hMF
  let : WeakEquivalence (simplexAllVertexComparisonDirect W k hk x ≫
      chosenSpineTupleFibreMap f k hk x) := inferInstance
  apply (weakEquivalence_iff (simplexAllVertexFibreMap f k x)).mp
  exact weakEquivalence_of_postcomp_of_fac
    (simplexAllVertexComparisonDirect_naturality f k hk x).symm

end SimplicialSpace.OriginalTupleMappingFibreWeakness
