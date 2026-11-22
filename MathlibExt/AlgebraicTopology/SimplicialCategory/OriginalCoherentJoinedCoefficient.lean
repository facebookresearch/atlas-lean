/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentJoinedIntervalFlags
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalFlagReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConcatenationFlags
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadOuterOperator
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace

/-!
# The SAME complete original joined coefficient

The actual union of both complete endpoint-interval inverses maps by the
SAME native joining ordinal to the full inverse of the original coherent
composition. Every original coefficient flag is retained in every scalar.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

private instance {J : Type u} [LinearOrder J] (a b : J)
    (p r : SimplicialThickening.Path a b) : Subsingleton (p ⟶ r) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The SAME full original joined coefficient is exactly the inverse of the original whole composition. -/
theorem joinedCoefficient {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c)
    {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))).obj q)
    (r : (nerve (SimplicialThickening.Path (ULift.up.{u} b) (ULift.up.{u} c))).obj q) :
    (OriginalBead.OuterOperator.map (joinedOperator a b c hab hbc)
      (joinedOperator_zero a b c hab hbc) (joinedOperator_last a b c hab hbc)).app q
      (OriginalFlaggedNecklace.ConcatFlags.coefficient
        ((homIso.{u} a b hab).inv.app q p) ((homIso.{u} b c hbc).inv.app q r)) =
      (homIso.{u} a c (hab.trans hbc)).inv.app q
        ((CompositionFace.composition (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c)).app q (p, r)) := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    let F := (joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u}
    let l :=
      (SSet.OriginalTwoBead.OrdinalCharts.prefixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u}
    let s :=
      (SSet.OriginalTwoBead.OrdinalCharts.suffixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u}
    have hL := homIso_inv_flags.{u} a b hab p t
    have hR := homIso_inv_flags.{u} b c hbc r t
    have hO := homIso_inv_flags.{u} a c (hab.trans hbc)
      ((CompositionFace.composition (ULift.up.{u} a) (ULift.up.{u} b) (ULift.up.{u} c)).app q (p, r)) t
    change F '' (l '' (((homIso.{u} a b hab).inv.app q p).obj t).I ∪
      s '' (((homIso.{u} b c hbc).inv.app q r).obj t).I) = _
    exact (congrArg (fun S => F '' S)
      (congrArg₂ (fun S T => l '' S ∪ s '' T) hL hR)).trans
        ((joined_image_preimages a b c hab hbc (p.obj t).I (r.obj t).I
          (fun k hk => ⟨(p.obj t).left_le k hk, (p.obj t).le_right k hk⟩)
          (fun k hk => ⟨(r.obj t).left_le k hk, (r.obj t).le_right k hk⟩)).trans hO.symm)
  · intro i j g
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.OriginalBeadInterval
