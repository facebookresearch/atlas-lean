/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PullbackFibreWeakDetection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original mapping fibres and the endpoint comparison

The original endpoint square and its chosen double pullbacks retain both
structural legs. All comparisons use the same original ordered vertex pairs.
The RF-only weak criterion is proved through the actual Kan factorization and
unpointed homotopy-pullback comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace

variable {W V : SimplicialSpace.{u}}

/-- The original endpoint pullback over the original outer-zero product map. -/
abbrev mappingEndpointPullback (f : W ⟶ V) : SSet.{u} :=
  pullback (mappingEndpoint V)
    (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))

/-- The entire original outer-one comparison, with the native square orientation. -/
def mappingEndpointComparison (f : W ⟶ V) : W.diagram _⦋1⦌ ⟶ mappingEndpointPullback f :=
  pullback.lift (f.hom.app (op ⦋1⦌)) (mappingEndpoint W)
    (mappingEndpoint_naturality f).symm

/-- The original comparison retains the entire outer-one map. -/
@[reassoc (attr := simp)]
theorem mappingEndpointComparison_fst (f : W ⟶ V) :
    mappingEndpointComparison f ≫ pullback.fst (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) =
      f.hom.app (op ⦋1⦌) := pullback.lift_fst _ _ _

/-- The original comparison retains the same endpoint map to the ordered product. -/
@[reassoc (attr := simp)]
theorem mappingEndpointComparison_snd (f : W ⟶ V) :
    mappingEndpointComparison f ≫ pullback.snd (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) =
      mappingEndpoint W := pullback.lift_snd _ _ _

/-- The chosen original target fibre over the same ordered pair of source vertices. -/
abbrev mappingEndpointTargetFibre (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback
    (pullback.snd (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
    (mappingPointPair W x y)

private theorem mappingEndpointTargetFibre_isPullback (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    IsPullback
      (pullback.fst (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) ≫
        pullback.fst (mappingEndpoint V)
          (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
      (pullback.snd (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y))
            (mappingEndpoint V)
      (mappingPointPair V (mappingVertexMap f x) (mappingVertexMap f y)) := by
  have h := (IsPullback.of_hasPullback
    (pullback.snd (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
    (mappingPointPair W x y)).paste_horiz
      (IsPullback.of_hasPullback (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
  rw [mappingPointPair_naturality] at h
  exact h

/-- The whole target fibre is the original target mapping fibre, with both original legs. -/
def mappingEndpointTargetFibreIso (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingEndpointTargetFibre f x y ≅
      mappingFibre V (mappingVertexMap f x) (mappingVertexMap f y) :=
  (mappingEndpointTargetFibre_isPullback f x y).isoIsPullback _ _
    (IsPullback.of_hasPullback (mappingEndpoint V)
      (mappingPointPair V (mappingVertexMap f x) (mappingVertexMap f y)))

/-- The forward target comparison retains its original outer-one projection. -/
@[reassoc]
theorem mappingEndpointTargetFibreIso_hom_fst (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y) =
      pullback.fst (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) ≫
        pullback.fst (mappingEndpoint V)
          (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) :=
  IsPullback.isoIsPullback_hom_fst _ _ (mappingEndpointTargetFibre_isPullback f x y)
    (IsPullback.of_hasPullback _ _)

/-- The forward target comparison retains the original Delta0 projection. -/
@[reassoc]
theorem mappingEndpointTargetFibreIso_hom_snd (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) =
      pullback.snd (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) :=
  IsPullback.isoIsPullback_hom_snd _ _ (mappingEndpointTargetFibre_isPullback f x y)
    (IsPullback.of_hasPullback _ _)

/-- The inverse target comparison recovers the original outer-one projection. -/
@[reassoc]
theorem mappingEndpointTargetFibreIso_inv_fst (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointTargetFibreIso f x y).inv ≫
        pullback.fst (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) ≫
          pullback.fst (mappingEndpoint V)
            (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) =
      mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y) := by
  rw [← Category.assoc]
  exact IsPullback.isoIsPullback_inv_fst _ _ (mappingEndpointTargetFibre_isPullback f x y)
    (IsPullback.of_hasPullback _ _)

/-- The inverse target comparison recovers the original Delta0 projection. -/
@[reassoc]
theorem mappingEndpointTargetFibreIso_inv_snd (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointTargetFibreIso f x y).inv ≫ pullback.snd (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) =
      mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) :=
  IsPullback.isoIsPullback_inv_snd _ _ (mappingEndpointTargetFibre_isPullback f x y)
    (IsPullback.of_hasPullback _ _)

/-- The inverse comparison retains the original base-product point equation. -/
@[reassoc]
theorem mappingEndpointTargetFibreIso_inv_base (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointTargetFibreIso f x y).inv ≫
        pullback.fst (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) ≫
          pullback.snd (mappingEndpoint V)
            (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) =
      mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) ≫
        mappingPointPair W x y := by
  rw [pullback.condition, ← Category.assoc, mappingEndpointTargetFibreIso_inv_snd]

/-- The actual chosen fibre map of the original endpoint comparison. -/
def mappingEndpointFibreMap (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ mappingEndpointTargetFibre f x y :=
  pullback.lift (mappingFibre.fst W x y ≫ mappingEndpointComparison f)
    (mappingFibre.snd W x y) (by
      rw [Category.assoc, mappingEndpointComparison_snd]
      exact mappingFibre.condition W x y)

/-- The induced fibre map retains the comparison followed by its original ambient inclusion. -/
@[reassoc (attr := simp)]
theorem mappingEndpointFibreMap_fst (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingEndpointFibreMap f x y ≫ pullback.fst (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) =
      mappingFibre.fst W x y ≫ mappingEndpointComparison f := pullback.lift_fst _ _ _

/-- The induced fibre map preserves the original Delta0 point leg. -/
@[reassoc (attr := simp)]
theorem mappingEndpointFibreMap_snd (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingEndpointFibreMap f x y ≫ pullback.snd (pullback.snd (mappingEndpoint V)
        (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) (mappingPointPair W x y) =
      mappingFibre.snd W x y := pullback.lift_snd _ _ _

/-- The actual target isomorphism identifies the induced map with the original mapping-fibre map. -/
@[reassoc]
theorem mappingEndpointFibreMap_comp_targetIso (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingEndpointFibreMap f x y ≫ (mappingEndpointTargetFibreIso f x y).hom =
      mappingFibre.map f (x := x) (y := y) rfl rfl := by
  apply pullback.hom_ext
  · change mappingEndpointFibreMap f x y ≫ (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y) =
      mappingFibre.map f (x := x) (y := y) rfl rfl ≫
        mappingFibre.fst V (mappingVertexMap f x) (mappingVertexMap f y)
    simp only [mappingEndpointTargetFibreIso_hom_fst,
      mappingEndpointFibreMap_fst_assoc, mappingEndpointComparison_fst,
      mappingFibre.map_fst]
  · change mappingEndpointFibreMap f x y ≫ (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y) =
      mappingFibre.map f (x := x) (y := y) rfl rfl ≫
        mappingFibre.snd V (mappingVertexMap f x) (mappingVertexMap f y)
    simp only [mappingEndpointTargetFibreIso_hom_snd,
      mappingEndpointFibreMap_snd, mappingFibre.map_snd]

/-- The whole Arrow identification keeps the ORIGINAL mapping-fibre source identity. -/
def mappingEndpointFibreArrowIso (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    Arrow.mk (mappingEndpointFibreMap f x y) ≅
      Arrow.mk (mappingFibre.map f (x := x) (y := y) rfl rfl) :=
  Arrow.isoMk (Iso.refl _) (mappingEndpointTargetFibreIso f x y)
    (by simpa using (mappingEndpointFibreMap_comp_targetIso f x y).symm)

end SimplicialSpace



namespace SimplicialSpace

variable {W V : SimplicialSpace.{u}}

/-- The forward whole Arrow comparison preserves the original mapping-fibre source identity. -/
@[simp]
theorem mappingEndpointFibreArrowIso_hom_left (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointFibreArrowIso f x y).hom.left = 𝟙 (mappingFibre W x y) := rfl

/-- The inverse whole Arrow comparison preserves the same source identity. -/
@[simp]
theorem mappingEndpointFibreArrowIso_inv_left (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointFibreArrowIso f x y).inv.left = 𝟙 (mappingFibre W x y) := rfl

/-- The forward whole Arrow target is the actual target-fibre isomorphism. -/
@[simp]
theorem mappingEndpointFibreArrowIso_hom_right (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointFibreArrowIso f x y).hom.right =
        (mappingEndpointTargetFibreIso f x y).hom := rfl

/-- The inverse whole Arrow target is the same original inverse isomorphism. -/
@[simp]
theorem mappingEndpointFibreArrowIso_inv_right (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (mappingEndpointFibreArrowIso f x y).inv.right =
        (mappingEndpointTargetFibreIso f x y).inv := rfl

/-- Every original inner operator commutes with the forward target-fibre identification. -/
theorem mappingEndpointTargetFibreIso_operator (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) :
    (mappingEndpointTargetFibre f x y).map a ≫ (mappingEndpointTargetFibreIso f x y).hom.app m =
      (mappingEndpointTargetFibreIso f x y).hom.app n ≫
        (mappingFibre V (mappingVertexMap f x) (mappingVertexMap f y)).map a :=
  (mappingEndpointTargetFibreIso f x y).hom.naturality a

/-- Every original inner operator commutes with its genuine inverse. -/
theorem mappingEndpointTargetFibreIso_inv_operator (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) :
    (mappingFibre V (mappingVertexMap f x) (mappingVertexMap f y)).map a ≫
        (mappingEndpointTargetFibreIso f x y).inv.app m =
      (mappingEndpointTargetFibreIso f x y).inv.app n ≫
        (mappingEndpointTargetFibre f x y).map a :=
  (mappingEndpointTargetFibreIso f x y).inv.naturality a

private theorem mappingEndpointLevel_kanComplex (W : SimplicialSpace.{u}) (n : ℕ) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → SSet.KanComplex (W.diagram _⦋n⦌) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hW
  let X := ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj (Δ[n] : SSet.{u}))
  have hK := ReedyModel.innerHom_kanComplex X W (ReedyModel.isCofibrant X) hW
  change SSet.KanComplex ((discreteSourceMapping W).obj (op (Δ[n] : SSet.{u}))) at hK
  let _ : IsFibrant ((discreteSourceMapping W).obj (op (Δ[n] : SSet.{u}))) := hK
  exact isFibrant_of_fibration (discreteYonedaIso W n).inv

private theorem mappingEndpointFibreMap_eq_sameBase (f : W ⟶ V)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback.map (mappingEndpoint W) (mappingPointPair W x y)
        (pullback.snd (mappingEndpoint V)
          (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
        (mappingPointPair W x y) (mappingEndpointComparison f) (𝟙 _) (𝟙 _)
        (by simp) (by simp) =
      mappingEndpointFibreMap f x y := by
  dsimp only [mappingEndpointFibreMap, mappingFibre, mappingFibre.fst,
    mappingFibre.snd, mappingEndpointTargetFibre]
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [pullback.lift_snd, Category.comp_id]
    exact (pullback.lift_snd _ _ _).symm

/-- At original Reedy-fibrant endpoints, all original mapping fibres detect full weakness of the
same endpoint comparison. -/
theorem mappingEndpointComparison_realizationWeak_iff (f : W ⟶ V) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → IsFibrant V →
      (SSet.realizationWeakEquivalences (mappingEndpointComparison f) ↔
        ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
          SSet.realizationWeakEquivalences (mappingFibre.map f (x := x) (y := y) rfl rfl)) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hW hV
  let _ : SSet.KanComplex (W.diagram _⦋0⦌) := mappingEndpointLevel_kanComplex W 0 hW
  let _ : Fibration (prod.fst : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌) :=
    (fibration_iff _).mpr ((fibrations SSet.{u}).of_isPullback
      (IsPullback.of_hasBinaryProduct' (W.diagram _⦋0⦌) (W.diagram _⦋0⦌)).flip
      ((fibration_iff (terminal.from (W.diagram _⦋0⦌))).mp inferInstance))
  let _ : SSet.KanComplex (W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌) :=
    isFibrant_of_fibration (prod.fst : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌)
  let _ : Fibration (mappingEndpoint W) := ReedyModel.mappingEndpoint_fibration W hW
  let _ : Fibration (mappingEndpoint V) := ReedyModel.mappingEndpoint_fibration V hV
  let _ : Fibration (pullback.snd (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))) := by infer_instance
  have hs := SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (mappingEndpointComparison f) (mappingEndpoint W)
    (pullback.snd (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
    (mappingEndpointComparison_snd f)
  refine hs.trans ?_
  constructor
  · intro hf x y
    apply (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (mappingEndpointFibreArrowIso f x y)).mp
    have h := hf (mappingPointPair W x y)
    dsimp only [mappingFibre, mappingEndpointTargetFibre] at h ⊢
    rw [mappingEndpointFibreMap_eq_sameBase] at h
    exact h
  · intro hf b
    obtain ⟨x, y, rfl⟩ : ∃ x y : (W.diagram _⦋0⦌) _⦋0⦌, mappingPointPair W x y = b := by
      let x : (W.diagram _⦋0⦌) _⦋0⦌ :=
        (prod.fst : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌).app (op ⦋0⦌)
          (SSet.yonedaEquiv b)
      let y : (W.diagram _⦋0⦌) _⦋0⦌ :=
        (prod.snd : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌).app (op ⦋0⦌)
          (SSet.yonedaEquiv b)
      refine ⟨x, y, ?_⟩
      apply prod.hom_ext
      · rw [mappingPointPair_fst]
        simpa only [x, Equiv.symm_apply_apply] using
          (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv b)
            (prod.fst : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌)).symm
      · rw [mappingPointPair_snd]
        simpa only [y, Equiv.symm_apply_apply] using
          (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv b)
            (prod.snd : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌)).symm
    have h := (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
      (mappingEndpointFibreArrowIso f x y)).mpr (hf x y)
    dsimp only [mappingFibre, mappingEndpointTargetFibre] at h ⊢
    rw [mappingEndpointFibreMap_eq_sameBase]
    exact h

/-- The same original criterion uses the full native Kan weak class on every original mapping
fibre. -/
theorem mappingEndpointComparison_realizationWeak_iff_kanWeak (f : W ⟶ V) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → IsFibrant V →
      (SSet.realizationWeakEquivalences (mappingEndpointComparison f) ↔
        ∀ x y : (W.diagram _⦋0⦌) _⦋0⦌,
          SSet.KanComplex.W (mappingFibre.map f (x := x) (y := y) rfl rfl)) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hW hV
  rw [mappingEndpointComparison_realizationWeak_iff f hW hV]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  let _ : SSet.KanComplex (mappingFibre W x y) := ReedyModel.mappingFibre_kanComplex W x y hW
  let _ : SSet.KanComplex (mappingFibre V (mappingVertexMap f x) (mappingVertexMap f y)) :=
    ReedyModel.mappingFibre_kanComplex V _ _ hV
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence
    (mappingFibre.map f (x := x) (y := y) rfl rfl)).symm


variable {W' V' : SimplicialSpace.{u}}

private theorem mappingEndpointBaseSquare (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r) :
    prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) ≫
        prod.map (r.hom.app (op ⦋0⦌)) (r.hom.app (op ⦋0⦌)) =
      prod.map (q.hom.app (op ⦋0⦌)) (q.hom.app (op ⦋0⦌)) ≫
        prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌)) := by
  have h₀ := congrArg (fun a : W ⟶ V' => a.hom.app (op ⦋0⦌)) h
  change q.hom.app (op ⦋0⦌) ≫ f'.hom.app (op ⦋0⦌) =
    f.hom.app (op ⦋0⦌) ≫ r.hom.app (op ⦋0⦌) at h₀
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
      congrArg (fun a => (prod.fst : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌) ≫ a) h₀.symm
  · simpa only [Category.assoc, prod.map_snd, prod.map_snd_assoc] using
      congrArg (fun a => (prod.snd : W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ ⟶ W.diagram _⦋0⦌) ≫ a) h₀.symm

/-- An original commuting square induces the actual endpoint-pullback map. -/
def mappingEndpointPullbackMap (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r) :
    mappingEndpointPullback f ⟶ mappingEndpointPullback f' :=
  pullback.map (mappingEndpoint V)
    (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)))
    (mappingEndpoint V')
    (prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌)))
    (r.hom.app (op ⦋1⦌))
    (prod.map (q.hom.app (op ⦋0⦌)) (q.hom.app (op ⦋0⦌)))
    (prod.map (r.hom.app (op ⦋0⦌)) (r.hom.app (op ⦋0⦌)))
    (mappingEndpoint_naturality r) (mappingEndpointBaseSquare f f' q r h)

/-- The whole endpoint-pullback map retains the original target outer-one component. -/
@[reassoc]
theorem mappingEndpointPullbackMap_fst (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r) :
    mappingEndpointPullbackMap f f' q r h ≫
        pullback.fst (mappingEndpoint V')
          (prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌))) =
      pullback.fst (mappingEndpoint V)
          (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) ≫ r.hom.app (op ⦋1⦌) :=
  pullback.lift_fst _ _ _

/-- The same map retains both original source outer-zero components. -/
@[reassoc]
theorem mappingEndpointPullbackMap_snd (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r) :
    mappingEndpointPullbackMap f f' q r h ≫
        pullback.snd (mappingEndpoint V')
          (prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌))) =
      pullback.snd (mappingEndpoint V)
          (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))) ≫
        prod.map (q.hom.app (op ⦋0⦌)) (q.hom.app (op ⦋0⦌)) :=
  pullback.lift_snd _ _ _

/-- The original endpoint comparison is natural for every original commuting square. -/
@[reassoc]
theorem mappingEndpointComparison_natural (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r) :
    mappingEndpointComparison f ≫ mappingEndpointPullbackMap f f' q r h =
      q.hom.app (op ⦋1⦌) ≫ mappingEndpointComparison f' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mappingEndpointPullbackMap_fst,
      mappingEndpointComparison_fst_assoc, mappingEndpointComparison_fst]
    exact (congrArg (fun a : W ⟶ V' => a.hom.app (op ⦋1⦌)) h).symm
  · simp only [Category.assoc, mappingEndpointPullbackMap_snd,
      mappingEndpointComparison_snd_assoc, mappingEndpointComparison_snd]
    exact mappingEndpoint_naturality q

/-- The original commuting square transports its image vertex to the prescribed source vertex
image. -/
theorem mappingEndpointImageVertex (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (x' : (W'.diagram _⦋0⦌) _⦋0⦌)
    (hx : mappingVertexMap q x = x') :
    mappingVertexMap r (mappingVertexMap f x) = mappingVertexMap f' x' := by
  calc
    _ = mappingVertexMap (f ≫ r) x := (mappingVertexMap_comp f r x).symm
    _ = mappingVertexMap (q ≫ f') x := congrArg (fun a => mappingVertexMap a x) h.symm
    _ = mappingVertexMap f' (mappingVertexMap q x) := mappingVertexMap_comp q f' x
    _ = _ := congrArg (mappingVertexMap f') hx

/-- The same square and prescribed moved vertices induce the actual double-pullback map. -/
def mappingEndpointTargetFibreMap (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (W'.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y') :
    mappingEndpointTargetFibre f x y ⟶ mappingEndpointTargetFibre f' x' y' :=
  pullback.map
    (pullback.snd (mappingEndpoint V)
      (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
    (mappingPointPair W x y)
    (pullback.snd (mappingEndpoint V')
      (prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌))))
    (mappingPointPair W' x' y')
    (mappingEndpointPullbackMap f f' q r h) (𝟙 (Δ[0] : SSet.{u}))
    (prod.map (q.hom.app (op ⦋0⦌)) (q.hom.app (op ⦋0⦌)))
    (mappingEndpointPullbackMap_snd f f' q r h).symm
    (by rw [mappingPointPair_naturality q, hx, hy, Category.id_comp])

/-- The moved double-pullback retains the entire original endpoint-pullback leg. -/
@[reassoc]
theorem mappingEndpointTargetFibreMap_fst (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (W'.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y') :
    mappingEndpointTargetFibreMap f f' q r h hx hy ≫
        pullback.fst
          (pullback.snd (mappingEndpoint V')
            (prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌))))
          (mappingPointPair W' x' y') =
      pullback.fst
          (pullback.snd (mappingEndpoint V)
            (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
          (mappingPointPair W x y) ≫ mappingEndpointPullbackMap f f' q r h :=
  pullback.lift_fst _ _ _

/-- The moved double-pullback preserves the same literal Delta0 leg. -/
@[reassoc]
theorem mappingEndpointTargetFibreMap_snd (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (W'.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y') :
    mappingEndpointTargetFibreMap f f' q r h hx hy ≫
        pullback.snd
          (pullback.snd (mappingEndpoint V')
            (prod.map (f'.hom.app (op ⦋0⦌)) (f'.hom.app (op ⦋0⦌))))
          (mappingPointPair W' x' y') =
      pullback.snd
          (pullback.snd (mappingEndpoint V)
            (prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌))))
          (mappingPointPair W x y) := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The forward whole target isomorphism preserves every original square and both moved vertices. -/
theorem mappingEndpointTargetFibreIso_natural (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (W'.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y') :
    mappingEndpointTargetFibreMap f f' q r h hx hy ≫ (mappingEndpointTargetFibreIso f' x' y').hom =
      (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.map r (mappingEndpointImageVertex f f' q r h x x' hx)
          (mappingEndpointImageVertex f f' q r h y y' hy) := by
  apply pullback.hom_ext
  · change mappingEndpointTargetFibreMap f f' q r h hx hy ≫
        (mappingEndpointTargetFibreIso f' x' y').hom ≫
          mappingFibre.fst V' (mappingVertexMap f' x') (mappingVertexMap f' y') =
      (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.map r (mappingEndpointImageVertex f f' q r h x x' hx)
          (mappingEndpointImageVertex f f' q r h y y' hy) ≫
            mappingFibre.fst V' (mappingVertexMap f' x') (mappingVertexMap f' y')
    simp only [mappingEndpointTargetFibreIso_hom_fst,
      mappingEndpointTargetFibreMap_fst_assoc, mappingEndpointPullbackMap_fst,
      mappingFibre.map_fst, mappingEndpointTargetFibreIso_hom_fst_assoc]
  · change mappingEndpointTargetFibreMap f f' q r h hx hy ≫
        (mappingEndpointTargetFibreIso f' x' y').hom ≫
          mappingFibre.snd V' (mappingVertexMap f' x') (mappingVertexMap f' y') =
      (mappingEndpointTargetFibreIso f x y).hom ≫
        mappingFibre.map r (mappingEndpointImageVertex f f' q r h x x' hx)
          (mappingEndpointImageVertex f f' q r h y y' hy) ≫
            mappingFibre.snd V' (mappingVertexMap f' x') (mappingVertexMap f' y')
    simp only [mappingEndpointTargetFibreIso_hom_snd,
      mappingEndpointTargetFibreMap_snd, mappingFibre.map_snd]

/-- The inverse whole target isomorphism preserves the same original square. -/
theorem mappingEndpointTargetFibreIso_inv_natural (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (W'.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y') :
    mappingFibre.map r (mappingEndpointImageVertex f f' q r h x x' hx)
        (mappingEndpointImageVertex f f' q r h y y' hy) ≫
          (mappingEndpointTargetFibreIso f' x' y').inv =
      (mappingEndpointTargetFibreIso f x y).inv ≫
          mappingEndpointTargetFibreMap f f' q r h hx hy := by
  apply (cancel_epi (mappingEndpointTargetFibreIso f x y).hom).mp
  rw [← Category.assoc, ← mappingEndpointTargetFibreIso_natural f f' q r h hx hy,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.hom_inv_id_assoc]

/-- The induced strict-fibre map is natural at every original commuting square and prescribed
pair. -/
theorem mappingEndpointFibreMap_natural (f : W ⟶ V) (f' : W' ⟶ V')
    (q : W ⟶ W') (r : V ⟶ V') (h : q ≫ f' = f ≫ r)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (W'.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y') :
    mappingEndpointFibreMap f x y ≫ mappingEndpointTargetFibreMap f f' q r h hx hy =
      mappingFibre.map q hx hy ≫ mappingEndpointFibreMap f' x' y' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mappingEndpointTargetFibreMap_fst,
      mappingEndpointFibreMap_fst_assoc, mappingEndpointFibreMap_fst,
      mappingEndpointComparison_natural f f' q r h, mappingFibre.map_fst_assoc]
  · rw [Category.assoc, mappingEndpointTargetFibreMap_snd,
      mappingEndpointFibreMap_snd, Category.assoc, mappingEndpointFibreMap_snd,
      mappingFibre.map_snd]

end SimplicialSpace
