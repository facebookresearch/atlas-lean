/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalFlagReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalImagePreimage
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadOuterOperator

/-!
# SAME full original endpoint-interval coefficient operators

The actual complete interval inverses commute with every original outer
operator through its SAME full interval restriction. The proof retains
all original path subsets and uses both actual inverse flag equations.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

private instance {J : Type u} [LinearOrder J] (a b : J)
    (p r : SimplicialThickening.Path a b) : Subsingleton (p ⟶ r) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The SAME whole original interval inverse commutes with the literal original outer coefficient map. -/
theorem intervalCoefficient_operator {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (a b : Fin (n + 1)) (hab : a ≤ b) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))).obj q) :
    (OriginalBead.OuterOperator.map (intervalOperator f a b hab)
      (intervalOperator_zero f a b hab) (intervalOperator_last f a b hab)).app q
      ((homIso.{u} a b hab).inv.app q p) =
        (homIso.{u} (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab)).inv.app q
          ((nerveMap (SimplicialThickening.functorMap f.toOrderHom.uliftMap
            (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)))).app q p) := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    change (intervalOperator f a b hab).toOrderHom.uliftMap ''
      (((homIso.{u} a b hab).inv.app q p).obj t).I = _
    have hL := homIso_inv_flags.{u} a b hab p t
    have hR := homIso_inv_flags.{u} (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab)
      ((nerveMap (SimplicialThickening.functorMap f.toOrderHom.uliftMap
        (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)))).app q p) t
    exact (congrArg (fun S => (intervalOperator f a b hab).toOrderHom.uliftMap '' S) hL).trans
      ((intervalOperator_image_preimage f a b hab (p.obj t).I
        (fun k hk => ⟨(p.obj t).left_le k hk, (p.obj t).le_right k hk⟩)).trans hR.symm)
  · intro i j g
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.OriginalBeadInterval
