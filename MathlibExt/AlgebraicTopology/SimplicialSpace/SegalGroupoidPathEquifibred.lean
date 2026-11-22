/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathOperatorWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.EquifibredDiagonalPullback

/-!
# The original fixed-object Segal groupoid path projection has weak operator comparisons

Every actual original operator edge is an equivalence in a Segal
groupoid. The proved original fibre transition is therefore weak at
each prescribed entire tail simplex. Both original row projections
are fibrations, so the genuine fibrewise criterion gives weakness of
the literal whole operator-relative pullback comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The actual whole operator-relative comparison of the original fixed-object path projection. -/
def relativeOperatorComparison {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (diagram W x).obj (op (SimplexCategory.mk n)) ⟶
      pullback ((projection W x).app (op (SimplexCategory.mk m))) (W.diagram.map f.op) :=
  SSet.EquifibredDiagonal.relativeComparison (projection W x) f

/-- The whole relative comparison target at the actual tail simplex is the original reindexed point fibre. -/
def relativePointTargetIso {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    pullback (pullback.snd ((projection W x).app (op (SimplexCategory.mk m))) (W.diagram.map f.op)) b ≅
      rowPointFibre W x m (b ≫ W.diagram.map f.op) :=
  pullbackLeftPullbackSndIso ((projection W x).app (op (SimplexCategory.mk m))) (W.diagram.map f.op) b

set_option backward.isDefEq.respectTransparency false in
/-- The entire relative point comparison is the actual original path point-fibre operator under native pasting. -/
theorem relativePointMap_eq {m n : ℕ} (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (b : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋n⦌) :
    pullback.map ((projection W x).app (op (SimplexCategory.mk n))) b
        (pullback.snd ((projection W x).app (op (SimplexCategory.mk m))) (W.diagram.map f.op)) b
        (relativeOperatorComparison W x f) (𝟙 _) (𝟙 _)
        (by simp [relativeOperatorComparison, SSet.EquifibredDiagonal.relativeComparison]) (by simp) ≫
      (relativePointTargetIso W x f b).hom = rowPointOperator W x f b := by
  apply pullback.hom_ext
  · simp only [relativePointTargetIso, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      relativeOperatorComparison, SSet.EquifibredDiagonal.relativeComparison, rowPointOperator,
      pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    rfl
  · simp only [relativePointTargetIso, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      rowPointOperator, pullback.map, pullback.lift_snd, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Every whole original operator-relative path comparison is weak when all actual original edges are equivalences. -/
theorem relativeOperatorComparison_weak {m n : ℕ} (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.realizationWeakEquivalences (relativeOperatorComparison W x f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ := projection_fibration W x hW.1 n
  let _ := projection_fibration W x hW.1 m
  let p := pullback.snd ((projection W x).app (op (SimplexCategory.mk m))) (W.diagram.map f.op)
  let _ : Fibration p := inferInstance
  have hf : relativeOperatorComparison W x f ≫ p =
      (projection W x).app (op (SimplexCategory.mk n)) := pullback.lift_snd _ _ _
  apply (SSet.realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    (relativeOperatorComparison W x f) ((projection W x).app (op (SimplexCategory.mk n))) p hf).mpr
  intro b
  have hb := rowPointOperator_weak W hW x f b (hG _)
  rw [← relativePointMap_eq] at hb
  exact (SSet.realizationWeakEquivalences.postcomp_iff _ _
    (SSet.realizationWeakEquivalences.of_isIso (relativePointTargetIso W x f b).hom)).mp hb

end SimplicialSpace.LeftDecalageObject
