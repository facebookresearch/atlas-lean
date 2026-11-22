/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalPathLeadingEdgeComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeSourceFibration

/-!
# The original leading-edge target projects fibrantly to the whole tail simplex

The original fixed-source leading-edge target is itself a pullback of
the original source-and-tail fibration. Its full tail projection is
therefore a Kan fibration at actual Reedy fibrancy. The original
source-edge target isomorphism transports this to its literal projection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.InitialEdgeTailMapping

/-- Fix the same original source while retaining the entire original tail object. -/
def fixedSourceTailPoint (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    W.diagram _⦋n⦌ ⟶ W.diagram _⦋0⦌ ⨯ W.diagram _⦋n⦌ :=
  prod.lift (SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.yonedaEquiv.symm x) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/-- The whole original fixed-source target is the actual pullback of the original source-and-tail map. -/
theorem fixedSourceTail_isPullback (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    IsPullback (pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x))
      (pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x) ≫
        pullback.fst (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)))
      (sourceTailMap W n) (fixedSourceTailPoint W x n) := by
  let a := rowSource W n
  let b := SSet.yonedaEquiv.symm x
  let t := pullback.fst (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2))
  have hw : pullback.fst a b ≫ sourceTailMap W n =
      (pullback.fst a b ≫ t) ≫ fixedSourceTailPoint W x n := by
    apply prod.hom_ext
    · simp only [Category.assoc, sourceTailMap, fixedSourceTailPoint, prod.lift_fst]
      have hp : (pullback.fst a b ≫ t) ≫ SSet.stdSimplex.isTerminalObj₀.from _ = pullback.snd a b :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      change pullback.fst a b ≫ a = (pullback.fst a b ≫ t) ≫ SSet.stdSimplex.isTerminalObj₀.from _ ≫ b
      calc
        _ = pullback.snd a b ≫ b := pullback.condition
        _ = ((pullback.fst a b ≫ t) ≫ SSet.stdSimplex.isTerminalObj₀.from _) ≫ b :=
          congrArg (fun q => q ≫ b) hp.symm
        _ = _ := Category.assoc _ _ _
    · simp only [Category.assoc, sourceTailMap, fixedSourceTailPoint, prod.lift_snd, Category.comp_id]
      rfl
  apply IsPullback.of_isLimit' (CommSq.mk hw)
  refine PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift s.fst (SSet.stdSimplex.isTerminalObj₀.from s.pt) ?_)
    (fun s => pullback.lift_fst _ _ _)
    (fun s => ?_)
    (fun s m hm hn => ?_)
  · have h := congrArg (fun q => q ≫ prod.fst) s.condition
    simp only [sourceTailMap, fixedSourceTailPoint, Category.assoc, prod.lift_fst] at h
    have hp : s.snd ≫ SSet.stdSimplex.isTerminalObj₀.from _ = SSet.stdSimplex.isTerminalObj₀.from s.pt :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    change s.fst ≫ a = (s.snd ≫ SSet.stdSimplex.isTerminalObj₀.from _) ≫ b at h
    rw [hp] at h
    exact h
  · rw [← Category.assoc, pullback.lift_fst]
    have h := congrArg (fun q => q ≫ prod.snd) s.condition
    simpa only [sourceTailMap, fixedSourceTailPoint, Category.assoc, prod.lift_snd, Category.comp_id] using h
  · apply pullback.hom_ext
    · exact hm.trans (pullback.lift_fst _ _ _).symm
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original full fixed-source target tail projection is a Kan fibration at Reedy fibrancy. -/
theorem sourceFibreTarget_tail_fibration (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration
      (pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x) ≫
        pullback.fst (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2))) := by
  intro hW n
  let _ := sourceTailMap_fibration W hW n
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact (fibrations SSet.{u}).of_isPullback (fixedSourceTail_isPullback W x n)
    ((HomotopicalAlgebra.fibration_iff _).mp (inferInstanceAs (Fibration (sourceTailMap W n))))

set_option backward.isDefEq.respectTransparency false in
/-- The original source-edge family target projects fibrantly to the same entire tail simplex. -/
theorem sourceEdgeTarget_tail_fibration (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration
      (pullback.snd (LeftDecalageObject.sourceEdgesTarget W x) (tailFirstVertex W n)) := by
  intro hW n
  let _ := sourceFibreTarget_tail_fibration W x hW n
  have he := sourceEdgeTargetIso_tail W x n
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  have h := (HomotopicalAlgebra.fibration_iff
    (pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x) ≫
      pullback.fst (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)))).mp
    (inferInstanceAs (Fibration (pullback.fst (rowSource W n) (SSet.yonedaEquiv.symm x) ≫
      pullback.fst (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)))))
  rw [← he] at h
  exact ((fibrations SSet.{u}).cancel_left_of_respectsIso
    (sourceEdgeTargetIso W x n).hom _).mp h

end SimplicialSpace.InitialEdgeTailMapping
