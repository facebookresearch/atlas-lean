/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.NerveCone
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Standard pullback cones for canonical coherent squares

Reindexing the lifted cospan along the native ULift equivalence gives a
standard WalkingCospan diagram. Native cospan and PullbackCone comparisons
identify its cone at the adjoined initial object with the ordinary pullback
of the four original square arrows. The coefficient object and Hom universes
remain independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory Limits

universe u uObj uHom

namespace SSet.NativePullback

variable {C : Type uObj} [Category.{uHom} C]

private theorem squareComm (Q : DiamondObjects.{u} ⥤ C) :
    Q.map (WithInitial.homTo (ULift.up WalkingCospan.left)) ≫
        Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶
          ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)) =
      Q.map (WithInitial.homTo (ULift.up WalkingCospan.right)) ≫
        Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶
          ULift.up WalkingCospan.one from WalkingCospan.Hom.inr)) := by
  rw [← Q.map_comp, ← Q.map_comp]
  congr 1

/-- The standard pullback cone supplied by the two actual initial square legs. -/
def ordinaryPullbackCone (Q : DiamondObjects.{u} ⥤ C) :
    PullbackCone
      (Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶
        ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)))
      (Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶
        ULift.up WalkingCospan.one from WalkingCospan.Hom.inr))) :=
  PullbackCone.mk (Q.map (WithInitial.homTo (ULift.up WalkingCospan.left)))
    (Q.map (WithInitial.homTo (ULift.up WalkingCospan.right))) (by exact squareComm Q)

private def ordinaryConeLimitEquiv (Q : DiamondObjects.{u} ⥤ C) :
    IsLimit ((ordinaryCone Q).whisker ULift.upFunctor) ≃ IsLimit (ordinaryPullbackCone Q) :=
  IsLimit.equivOfNatIsoOfIso (diagramIsoCospan (ULift.upFunctor ⋙ (cospanInclusionFunctor ⋙ Q)))
    ((ordinaryCone Q).whisker ULift.upFunctor) (ordinaryPullbackCone Q)
    (PullbackCone.isoMk ((ordinaryCone Q).whisker ULift.upFunctor))

/-- The canonical ordinary cone is limiting exactly when the four original arrows form a pullback. -/
theorem ordinaryCone_isLimit_iff_isPullback (Q : DiamondObjects.{u} ⥤ C) :
    Nonempty (IsLimit (ordinaryCone Q)) ↔
      IsPullback
        (Q.map (WithInitial.homTo (ULift.up WalkingCospan.left)))
        (Q.map (WithInitial.homTo (ULift.up WalkingCospan.right)))
        (Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶
          ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)))
        (Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶
          ULift.up WalkingCospan.one from WalkingCospan.Hom.inr))) := by
  constructor
  · rintro ⟨h⟩
    exact IsPullback.of_isLimit_cone (h.whiskerEquivalence ULift.equivalence)
  · intro h
    exact ⟨IsLimit.ofWhiskerEquivalence ULift.equivalence
      ((ordinaryConeLimitEquiv Q).symm h.isLimit)⟩

end SSet.NativePullback
