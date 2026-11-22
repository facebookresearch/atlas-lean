/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalEveryVertexComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFiniteKanProductWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalAllVertexReedyFibration
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalPowerMappingEndpointHomotopyFibre
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Every original vertex and the whole relative pullback

The actual relative comparison is weak precisely when every prescribed original
tuple-fibre map is weak. Its target is flattened by the native whole pullback
pasting Iso, with both projections retained. Reedy fibrancy belongs to the two
spaces; no fibration of the comparison or Segalness of its target is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SSet.modelCategoryQuillen.modelCategory
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace.OriginalAllVertexComparison
open FixedTupleSpinePrefix OriginalChosenSpineFixedTupleBaseChange

/-- Actual finite Kan products follow from the already proved full identity product map. -/
theorem finPi_kanComplex (n : ℕ) (X : Fin n → SSet.{u})
    [∀ i, SSet.KanComplex (X i)] : SSet.KanComplex (∏ᶜ X) := by
  have h := SSet.OriginalFiniteKanProducts.W.finPiMap n X X
    (fun i => 𝟙 (X i)) (fun i => SSet.KanComplex.W.ofIso (Iso.refl (X i)))
  exact h.kanComplex_source

/-- Native enriched mapping fibrancy gives the actual degree-zero object, through Yoneda. -/
theorem reedy_zero_kanComplex (W : SimplicialSpace.{u}) (hW : IsFibrant W) :
    SSet.KanComplex (W.diagram _⦋0⦌) := by
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[0] : SSet.{u}))
  have h := ReedyModel.innerHom_kanComplex X W (ReedyModel.isCofibrant X) hW
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) at h
  let _ : IsFibrant ((discreteSourceMapping W).obj (op (Δ[0] : SSet.{u}))) := h
  exact isFibrant_of_fibration (discreteYonedaIso W 0).inv

/-- The entire prescribed-vertex base is Kan, including every original arity. -/
theorem tupleVertexBase_kanComplex (W : SimplicialSpace.{u})
    (hW : IsFibrant W) (k : ℕ) : SSet.KanComplex (tupleVertexBase W k) := by
  let _ : SSet.KanComplex (W.diagram _⦋0⦌) := reedy_zero_kanComplex W hW
  exact finPi_kanComplex (k + 1) (fun _ => W.diagram _⦋0⦌)

/-- The literal original map into the target simplex pulled back over the entire source tuple. -/
def simplexAllVertexRelativeMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) (k : ℕ) :
    W.diagram _⦋k⦌ ⟶ pullback (simplexAllVertexMap V k) (originalTupleBaseMap f k) :=
  pullback.lift (f.hom.app (op ⦋k⦌)) (simplexAllVertexMap W k)
    (simplexAllVertexMap_naturality f k)

/-- Both whole relative projections are the actual degree-k map and original all-vertex map. -/
theorem simplexAllVertexRelativeMap_legs {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) :
    simplexAllVertexRelativeMap f k ≫ pullback.fst _ _ = f.hom.app (op ⦋k⦌) ∧
    simplexAllVertexRelativeMap f k ≫ pullback.snd _ _ = simplexAllVertexMap W k := by
  constructor <;> simp only [simplexAllVertexRelativeMap, pullback.lift_fst, pullback.lift_snd]

/-- The native same-base point map keeps the actual comparison and the identity Delta0 leg. -/
def simplexAllVertexRelativePointMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexFibre W k x ⟶
      pullback (pullback.snd (simplexAllVertexMap V k) (originalTupleBaseMap f k))
        (tuplePoint W k x) :=
  pullback.map _ _ _ _ (simplexAllVertexRelativeMap f k) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using (simplexAllVertexRelativeMap_legs f k).2.symm)
    (by simp only [Category.id_comp, Category.comp_id])

/-- Native whole pasting and the proved tuple-point naturality flatten the actual target. -/
def simplexAllVertexRelativeTargetIso {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback (pullback.snd (simplexAllVertexMap V k) (originalTupleBaseMap f k))
      (tuplePoint W k x) ≅
        simplexAllVertexFibre V k (fun i => mappingVertexMap f (x i)) :=
  pullbackLeftPullbackSndIso (simplexAllVertexMap V k) (originalTupleBaseMap f k)
      (tuplePoint W k x) ≪≫
    pullback.congrHom rfl (originalTuplePoint_naturality f k x)

/-- The first whole target projection retains both nested ambient projections. -/
@[reassoc]
theorem simplexAllVertexRelativeTargetIso_hom_fst {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    (simplexAllVertexRelativeTargetIso f k x).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst (simplexAllVertexMap V k) (originalTupleBaseMap f k) := by
  simp only [simplexAllVertexRelativeTargetIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The second whole target projection is the unchanged original Delta0 projection. -/
@[reassoc]
theorem simplexAllVertexRelativeTargetIso_hom_snd {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    (simplexAllVertexRelativeTargetIso f k x).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp only [simplexAllVertexRelativeTargetIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

/-- Both actual point-map legs identify the flattened map with the original simplex-fibre map. -/
theorem simplexAllVertexRelativePointMap_comp_targetIso {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    simplexAllVertexRelativePointMap f k x ≫
        (simplexAllVertexRelativeTargetIso f k x).hom = simplexAllVertexFibreMap f k x := by
  apply pullback.hom_ext
  · simp only [Category.assoc, simplexAllVertexRelativeTargetIso_hom_fst,
      simplexAllVertexRelativePointMap, pullback.map, pullback.lift_fst,
      pullback.lift_fst_assoc, simplexAllVertexRelativeMap, simplexAllVertexFibreMap]
  · simp only [Category.assoc, simplexAllVertexRelativeTargetIso_hom_snd,
      simplexAllVertexRelativePointMap, pullback.map, pullback.lift_snd,
      Category.comp_id, simplexAllVertexFibreMap]

/-- Every Delta0 point of the whole product yields all original coordinate vertices. -/
def tupleVerticesOfPoint (W : SimplicialSpace.{u}) (k : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ tupleVertexBase W k) :
    Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌ :=
  fun i => SSet.yonedaEquiv (b ≫ CategoryTheory.Limits.Pi.π _ i)

/-- No point is lost when all its actual coordinate vertices are reassembled. -/
theorem tuplePoint_tupleVerticesOfPoint (W : SimplicialSpace.{u}) (k : ℕ)
    (b : (Δ[0] : SSet.{u}) ⟶ tupleVertexBase W k) :
    tuplePoint W k (tupleVerticesOfPoint W k b) = b := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  simp only [tuplePoint, tupleVerticesOfPoint, CategoryTheory.Limits.Pi.lift_comp_π,
    Equiv.symm_apply_apply]

/-- Native same-base fibre detection applies with two actual fibrations and no Fibration(f). -/
theorem simplexAllVertexRelativeMap_weak_iff {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) (hW : IsFibrant W) (hV : IsFibrant V) :
    SSet.realizationWeakEquivalences (simplexAllVertexRelativeMap f k) ↔
      ∀ x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌,
        SSet.realizationWeakEquivalences (simplexAllVertexFibreMap f k x) := by
  let _ : SSet.KanComplex (tupleVertexBase W k) := tupleVertexBase_kanComplex W hW k
  let _ : Fibration (simplexAllVertexMap W k) :=
    OriginalAllVertexReedy.allVertexMap_fibration W k hW
  let _ : Fibration (simplexAllVertexMap V k) :=
    OriginalAllVertexReedy.allVertexMap_fibration V k hV
  let _ : Fibration (pullback.snd (simplexAllVertexMap V k) (originalTupleBaseMap f k)) :=
    inferInstance
  have criterion := SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (simplexAllVertexRelativeMap f k) (simplexAllVertexMap W k)
    (pullback.snd (simplexAllVertexMap V k) (originalTupleBaseMap f k))
    (simplexAllVertexRelativeMap_legs f k).2
  constructor
  · intro h x
    have hp : SSet.realizationWeakEquivalences (simplexAllVertexRelativePointMap f k x) :=
      criterion.mp h (tuplePoint W k x)
    have hiso : SSet.realizationWeakEquivalences (simplexAllVertexRelativeTargetIso f k x).hom :=
      (weakEquivalence_iff (simplexAllVertexRelativeTargetIso f k x).hom).mp
        (inferInstanceAs (WeakEquivalence (simplexAllVertexRelativeTargetIso f k x).hom))
    rw [← simplexAllVertexRelativePointMap_comp_targetIso]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ hp hiso
  · intro h
    apply criterion.mpr
    intro b
    let x := tupleVerticesOfPoint W k b
    have e : tuplePoint W k x = b := tuplePoint_tupleVerticesOfPoint W k b
    rw [← e]
    change SSet.realizationWeakEquivalences (simplexAllVertexRelativePointMap f k x)
    have hiso : SSet.realizationWeakEquivalences (simplexAllVertexRelativeTargetIso f k x).hom :=
      (weakEquivalence_iff (simplexAllVertexRelativeTargetIso f k x).hom).mp
        (inferInstanceAs (WeakEquivalence (simplexAllVertexRelativeTargetIso f k x).hom))
    apply (SSet.realizationWeakEquivalences.postcomp_iff _ _ hiso).mp
    rw [simplexAllVertexRelativePointMap_comp_targetIso]
    exact h x

end SimplicialSpace.OriginalAllVertexComparison
