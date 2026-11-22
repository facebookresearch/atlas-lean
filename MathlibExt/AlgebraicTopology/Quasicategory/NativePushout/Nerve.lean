/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.NativePushout.Cone
import MathlibExt.AlgebraicTopology.Quasicategory.NativePushout.Opposite
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Nerve

/-!
# Native pushouts in ordinary category nerves

The original square functor supplies its four original arrows and its actual
terminal-object cocone. Reversing its entire nerve, using the original native
pullback comparison, and reversing the ordinary universal property proves
that the native all-boundary condition is precisely the ordinary pushout.
The original category retains independent object and morphism universes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe uObj uHom aObj aHom bObj bHom

namespace SSet.NativePushout

variable {C : Type uObj} [Category.{uHom} C]

/-- The original native nerve map, reusing the canonical map for Hom-universe-zero indices. -/
abbrev nerveMapIndex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    squareShape.{max uObj uHom} ⟶ nerve C := NativePullback.nerveMapIndex Q

/-- The first original span arrow of the square functor. -/
abbrev topMap (Q : DiamondObjects.{max uObj uHom} ⥤ C) :=
  Q.map (WithTerminal.incl.map (show (ULift.up WalkingSpan.zero : SpanObjects.{max uObj uHom}) ⟶
    ULift.up WalkingSpan.left from WalkingSpan.Hom.fst))

/-- The second original span arrow of the square functor. -/
abbrev leftMap (Q : DiamondObjects.{max uObj uHom} ⥤ C) :=
  Q.map (WithTerminal.incl.map (show (ULift.up WalkingSpan.zero : SpanObjects.{max uObj uHom}) ⟶
    ULift.up WalkingSpan.right from WalkingSpan.Hom.snd))

/-- The first original terminal cocone leg of the square functor. -/
abbrev rightMap (Q : DiamondObjects.{max uObj uHom} ⥤ C) :=
  Q.map (WithTerminal.homFrom (ULift.up WalkingSpan.left))

/-- The second original terminal cocone leg of the square functor. -/
abbrev bottomMap (Q : DiamondObjects.{max uObj uHom} ⥤ C) :=
  Q.map (WithTerminal.homFrom (ULift.up WalkingSpan.right))

/-- The actual opposite square functor retains the entire original diagram. -/
def oppositeDiagram (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    NativePullback.DiamondObjects.{max uObj uHom} ⥤ Cᵒᵖ :=
  (squareOppToPushout ⋙ Q).rightOp

/-- Reversing a whole chain mapped through the actual right-opposite functor
recovers the same original reversed chain and all its arrows. -/
private theorem unop_map_rightOp {A : Type aObj} [Category.{aHom} A]
    {B : Type bObj} [Category.{bHom} B] (F : Aᵒᵖ ⥤ B)
    (n : ℕ) (s : ComposableArrows A n) :
    ComposableArrows.unop (s ⋙ F.rightOp) = s.op ⋙ F := by
  have hobj : ∀ i, (ComposableArrows.unop (s ⋙ F.rightOp)).obj i =
      (s.op ⋙ F).obj i := fun i => by
    simp only [ComposableArrows.unop_obj, Functor.comp_obj, Functor.rightOp_obj,
      unop_op, ComposableArrows.op_obj]
  refine ComposableArrows.ext hobj (fun i hi => ?_)
  refine (conj_eqToHom_iff_heq _ _ (hobj _) (hobj _)).mpr ?_
  simp only [ComposableArrows.map', ComposableArrows.unop_map,
    Functor.comp_map, Functor.rightOp_map, Quiver.Hom.unop_op, ComposableArrows.op_map]
  rfl

/-- Reversal of the native square nerve is the nerve of the actual opposite square functor. -/
theorem oppositeSquare_nerveMapIndex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    oppositeSquare (nerveMapIndex Q) =
      NativePullback.nerveMapIndex (oppositeDiagram Q) ≫ (nerveOppositeSimplicialIso C).hom := by
  apply NatTrans.ext
  funext d
  cases d with | op d =>
    cases d with | mk n =>
      apply ConcreteCategory.hom_ext
      intro s
      apply opObjEquiv.injective
      change s.op ⋙ (squareOppToPushout ⋙ Q) =
        ComposableArrows.unop (s ⋙ (squareOppToPushout ⋙ Q).rightOp)
      exact (unop_map_rightOp (squareOppToPushout ⋙ Q) n s).symm

/-- The actual native boundary condition is the original ordinary pushout
universal property of all four original arrows. -/
theorem isPushoutSquare_nerve_iff_isPushout (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    IsPushoutSquare (nerveMapIndex Q) ↔
      IsPushout (topMap Q) (leftMap Q) (rightMap Q) (bottomMap Q) := by
  have h := isPushoutSquare_iff_isPullbackSquare_opposite (nerveMapIndex Q)
  rw [oppositeSquare_nerveMapIndex] at h
  have hnative : IsPushoutSquare (nerveMapIndex Q) ↔
      NativePullback.IsPullbackSquare (NativePullback.nerveMapIndex (oppositeDiagram Q)) :=
    h.trans (NativePullback.isPullbackSquare_iff_of_iso
      (NativePullback.nerveMapIndex (oppositeDiagram Q)) (nerveOppositeSimplicialIso C)).symm
  have hord := NativePullback.isPullbackSquare_nerve_iff_isPullback (oppositeDiagram Q)
  change NativePullback.IsPullbackSquare (NativePullback.nerveMapIndex (oppositeDiagram Q)) ↔
    IsPullback (rightMap Q).op (bottomMap Q).op (topMap Q).op (leftMap Q).op at hord
  refine hnative.trans (hord.trans ?_)
  constructor
  · intro hp
    exact hp.unop.flip
  · intro hp
    exact hp.op.flip

/-- The original coherent square supplies its actual ordinary terminal-vertex cocone. -/
def ordinaryPushoutCocone (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    PushoutCocone (topMap Q) (leftMap Q) :=
  PushoutCocone.mk (rightMap Q) (bottomMap Q) (by
    rw [← Q.map_comp, ← Q.map_comp]
    congr 1)

/-- The ordinary cocone retains the original adjoined terminal square vertex. -/
theorem ordinaryPushoutCocone_pt (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (ordinaryPushoutCocone Q).pt = Q.obj WithTerminal.star := rfl

/-- The native all-boundary condition is the actual colimit of the original ordinary cocone. -/
theorem isPushoutSquare_nerve_iff_isColimit (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    IsPushoutSquare (nerveMapIndex Q) ↔ Nonempty (IsColimit (ordinaryPushoutCocone Q)) := by
  refine (isPushoutSquare_nerve_iff_isPushout Q).trans ?_
  constructor
  · intro hp
    exact ⟨hp.isColimit⟩
  · rintro ⟨hp⟩
    exact IsPushout.of_isColimit hp

end SSet.NativePushout
