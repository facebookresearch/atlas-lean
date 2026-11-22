/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalagePairFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpFibrations

/-!
# The fixed-object original left-decalage projection has fibrant and sharp rows

At each original degree, pull back the full right-face/first-object
restriction along the same original fixed object. The resulting entire
row projection is a Kan fibration at actual Reedy fibrancy. Its original
sharpness follows from the genuine fibration comparison theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.LeftDecalageObject

/-- The actual right-row object and same original fixed first object give the native product base map. -/
def pairPoint (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    W.diagram.obj (op (SimplexCategory.mk n)) ⟶
      W.diagram.obj (op (SimplexCategory.mk n)) ⨯ W.diagram.obj (op (SimplexCategory.mk 0)) :=
  prod.lift (𝟙 _) (SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.yonedaEquiv.symm x)

set_option backward.isDefEq.respectTransparency false in
/-- The complete original scalar fixed-source row is the pullback of the whole native pair map. -/
theorem scalarPairPullback (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    IsPullback (pullback.fst ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x))
      (pullback.fst ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x) ≫
          W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op)
      (LeftDecalageRows.pairMap W n) (pairPoint W x n) := by
  let a := (SimplicialObject.LeftDecalage.augmentation W.diagram).app (op (SimplexCategory.mk n))
  let b := SSet.yonedaEquiv.symm x
  let t := W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op
  have hw : (pullback.fst a b) ≫ LeftDecalageRows.pairMap W n =
      (pullback.fst a b ≫ t) ≫ pairPoint W x n := by
    apply prod.hom_ext
    · simp only [Category.assoc, LeftDecalageRows.pairMap, pairPoint, prod.lift_fst, Category.comp_id]
      rfl
    · simp only [Category.assoc, LeftDecalageRows.pairMap, pairPoint, prod.lift_snd]
      have hp : (pullback.fst a b ≫ t) ≫ SSet.stdSimplex.isTerminalObj₀.from _ = pullback.snd a b :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      change pullback.fst a b ≫ a = (pullback.fst a b ≫ t) ≫
        SSet.stdSimplex.isTerminalObj₀.from _ ≫ b
      calc
        _ = pullback.snd a b ≫ b := pullback.condition
        _ = ((pullback.fst a b ≫ t) ≫ SSet.stdSimplex.isTerminalObj₀.from _) ≫ b :=
          congrArg (fun q => q ≫ b) hp.symm
        _ = _ := Category.assoc _ _ _
  apply IsPullback.of_isLimit' (CommSq.mk hw)
  refine PullbackCone.IsLimit.mk _
    (fun s => pullback.lift s.fst
      (SSet.stdSimplex.isTerminalObj₀.from s.pt) ?_)
    (fun s => pullback.lift_fst _ _ _)
    (fun s => ?_)
    (fun s m hm hn => ?_)
  · have h := congrArg (fun q => q ≫ prod.snd) s.condition
    simp only [LeftDecalageRows.pairMap, pairPoint, Category.assoc, prod.lift_snd] at h
    have hp : s.snd ≫ SSet.stdSimplex.isTerminalObj₀.from _ =
        SSet.stdSimplex.isTerminalObj₀.from s.pt :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    change s.fst ≫ a = (s.snd ≫ SSet.stdSimplex.isTerminalObj₀.from _) ≫ b at h
    rw [hp] at h
    exact h
  · rw [← Category.assoc, pullback.lift_fst]
    have h := congrArg (fun q => q ≫ prod.fst) s.condition
    simpa only [LeftDecalageRows.pairMap, pairPoint, Category.assoc,
      prod.lift_fst, Category.comp_id] using h
  · apply pullback.hom_ext
    · exact hm.trans (pullback.lift_fst _ _ _).symm
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

set_option backward.isDefEq.respectTransparency false in
/-- The actual original scalar fixed-object row projection is a Kan fibration at Reedy fibrancy. -/
theorem scalar_projection_fibration (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ,
      Fibration (pullback.fst ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
        (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x) ≫
          W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op) := by
  intro hW n
  let _ := LeftDecalageRows.pairMap_fibration W hW n
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact (fibrations SSet.{u}).of_isPullback (scalarPairPullback W x n)
    ((HomotopicalAlgebra.fibration_iff _).mp (inferInstanceAs (Fibration (LeftDecalageRows.pairMap W n))))

set_option backward.isDefEq.respectTransparency false in
/-- Every whole original fixed-object path row projection is a Kan fibration at actual Reedy fibrancy. -/
theorem projection_fibration (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration ((projection W x).app (op (SimplexCategory.mk n))) := by
  intro hW n
  let p := pullback.fst ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
      (op (SimplexCategory.mk n))) (SSet.yonedaEquiv.symm x) ≫
        W.diagram.map (SimplexCategory.δ (0 : Fin (n + 2))).op
  let _ : Fibration p := scalar_projection_fibration W x hW n
  have he : (projection W x).app (op (SimplexCategory.mk n)) = (rowIso W x n).hom ≫ p := by
    dsimp only [p]
    rw [← Category.assoc, rowIso_fst]
    change (toDecalage W x).app (op (SimplexCategory.mk n)) ≫
        W.diagram.map (SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n)).op = _
    rw [SimplicialObject.LeftDecalage.rightBlock_delta]
  rw [he]
  infer_instance

/-- All actual fixed-object path projection rows are sharp on their same original bases. -/
theorem projection_sharp (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, SSet.SharpComparisonDraft.Sharp
      ((projection W x).app (op (SimplexCategory.mk n))) := by
  intro hW n
  let _ := projection_fibration W x hW n
  exact SSet.SharpComparisonDraft.sharp_of_fibration _

end SimplicialSpace.LeftDecalageObject
