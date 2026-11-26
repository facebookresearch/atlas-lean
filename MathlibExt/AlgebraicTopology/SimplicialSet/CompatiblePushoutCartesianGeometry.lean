/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SSet.RezkCompatiblePushout

/-- The two strict input faces of a mono pushout cube produce both strict
output faces and both original expressions for the intersection face. -/
theorem strict_faces {X0 X1 X2 PX Y0 Y1 Y2 PY : SSet.{u}}
    {u0 : X0 ⟶ X1} {v0 : X0 ⟶ X2} {a : Y0 ⟶ Y1} {b : Y0 ⟶ Y2}
    {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
    {p0 : X0 ⟶ Y0} {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
    [Mono b] (sx : IsPushout u0 v0 ix1 ix2) (sy : IsPushout a b iy1 iy2)
    (leftPB : IsPullback u0 p0 p1 a) (rightPB : IsPullback v0 p0 p2 b)
    (leftComm : CommSq ix1 p1 p iy1) (rightComm : CommSq ix2 p2 p iy2) :
    IsPullback ix1 p1 p iy1 ∧ IsPullback ix2 p2 p iy2 ∧
      IsPullback (u0 ≫ ix1) p0 p (a ≫ iy1) ∧
      IsPullback (v0 ≫ ix2) p0 p (b ≫ iy2) := by
  have h := ((Adhesive.van_kampen' sy)
    u0 v0 ix1 ix2 p0 p1 p2 p leftPB rightPB leftComm rightComm sx.toCommSq).mp sx
  exact ⟨h.1, h.2, leftPB.paste_horiz h.1, rightPB.paste_horiz h.2⟩

/-- Universal binary coproducts assemble the two actual piece pullbacks
into the literal cover square. The sharpness of its left arrow is not an input. -/
theorem coverSquare {X1 X2 PX Y1 Y2 PY : SSet.{u}}
    {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
    {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
    (leftPB : IsPullback ix1 p1 p iy1) (rightPB : IsPullback ix2 p2 p iy2) :
    IsPullback (coprod.desc ix1 ix2) (coprod.map p1 p2)
      p (coprod.desc iy1 iy2) := by
  let X : WalkingPair → SSet.{u} := pairFunction X1 X2
  let Y : WalkingPair → SSet.{u} := pairFunction Y1 Y2
  let ca : Cofan Y := BinaryCofan.mk
    (coprod.inl : Y1 ⟶ Y1 ⨿ Y2) coprod.inr
  let cd : Cofan X := BinaryCofan.mk
    (coprod.inl : X1 ⟶ X1 ⨿ X2) coprod.inr
  let f : (j : WalkingPair) → Y j ⟶ PY :=
    fun j => WalkingPair.casesOn j iy1 iy2
  let q1 : (j : WalkingPair) → X j ⟶ PX :=
    fun j => WalkingPair.casesOn j ix1 ix2
  let q2 : (j : WalkingPair) → X j ⟶ Y j :=
    fun j => WalkingPair.casesOn j p1 p2
  have ha : IsUniversalColimit ca :=
    FinitaryPreExtensive.universal' ca (coprodIsCoprod Y1 Y2)
  have hd : IsColimit cd := coprodIsCoprod X1 X2
  have hP (j : WalkingPair) : IsPullback (q1 j) (q2 j) p (f j) := by
    cases j
    · exact leftPB
    · exact rightPB
  have hu (j : WalkingPair) : ca.inj j ≫ coprod.desc iy1 iy2 = f j := by
    cases j
    · change coprod.inl ≫ coprod.desc iy1 iy2 = iy1
      exact coprod.inl_desc iy1 iy2
    · change coprod.inr ≫ coprod.desc iy1 iy2 = iy2
      exact coprod.inr_desc iy1 iy2
  have h := ha.isPullback_of_isColimit_left f (coprod.desc iy1 iy2) p
    q1 q2 hP hd hu
  have htop : Cofan.IsColimit.desc hd q1 = coprod.desc ix1 ix2 := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ Cofan.IsColimit.desc hd q1 = ix1 :=
          Cofan.IsColimit.fac hd q1 WalkingPair.left
        _ = coprod.inl ≫ coprod.desc ix1 ix2 := (coprod.inl_desc ix1 ix2).symm
    · calc
        coprod.inr ≫ Cofan.IsColimit.desc hd q1 = ix2 :=
          Cofan.IsColimit.fac hd q1 WalkingPair.right
        _ = coprod.inr ≫ coprod.desc ix1 ix2 := (coprod.inr_desc ix1 ix2).symm
  have hleft : Cofan.IsColimit.desc hd (fun j => q2 j ≫ ca.inj j) =
      coprod.map p1 p2 := by
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ Cofan.IsColimit.desc hd (fun j => q2 j ≫ ca.inj j) =
            p1 ≫ coprod.inl :=
          Cofan.IsColimit.fac hd (fun j => q2 j ≫ ca.inj j) WalkingPair.left
        _ = coprod.inl ≫ coprod.map p1 p2 := (coprod.inl_map p1 p2).symm
    · calc
        coprod.inr ≫ Cofan.IsColimit.desc hd (fun j => q2 j ≫ ca.inj j) =
            p2 ≫ coprod.inr :=
          Cofan.IsColimit.fac hd (fun j => q2 j ≫ ca.inj j) WalkingPair.right
        _ = coprod.inr ≫ coprod.map p1 p2 := (coprod.inr_map p1 p2).symm
  simpa only [htop, hleft] using h

/-- The actual sum of the original sources is the chosen pullback of the
original pushout cover. -/
def coverIso {X1 X2 PX Y1 Y2 PY : SSet.{u}}
    {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
    {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
    (leftPB : IsPullback ix1 p1 p iy1) (rightPB : IsPullback ix2 p2 p iy2) :
    X1 ⨿ X2 ≅ pullback p (coprod.desc iy1 iy2) :=
  (coverSquare leftPB rightPB).isoPullback

/-- All four forward and inverse projections of the same cover isomorphism. -/
theorem coverIso_legs {X1 X2 PX Y1 Y2 PY : SSet.{u}}
    {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
    {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
    (leftPB : IsPullback ix1 p1 p iy1) (rightPB : IsPullback ix2 p2 p iy2) :
    (coverIso leftPB rightPB).hom ≫ pullback.fst p (coprod.desc iy1 iy2) =
        coprod.desc ix1 ix2 ∧
      (coverIso leftPB rightPB).hom ≫ pullback.snd p (coprod.desc iy1 iy2) =
        coprod.map p1 p2 ∧
      (coverIso leftPB rightPB).inv ≫ coprod.desc ix1 ix2 =
        pullback.fst p (coprod.desc iy1 iy2) ∧
      (coverIso leftPB rightPB).inv ≫ coprod.map p1 p2 =
        pullback.snd p (coprod.desc iy1 iy2) := by
  exact ⟨(coverSquare leftPB rightPB).isoPullback_hom_fst,
    (coverSquare leftPB rightPB).isoPullback_hom_snd,
    (coverSquare leftPB rightPB).isoPullback_inv_fst,
    (coverSquare leftPB rightPB).isoPullback_inv_snd⟩

/-- Whole Arrow comparison: the codomain remains the original coproduct.
The pulled-back cover arrow is the SECOND pullback projection. -/
def coverArrowIso {X1 X2 PX Y1 Y2 PY : SSet.{u}}
    {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
    {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
    (leftPB : IsPullback ix1 p1 p iy1) (rightPB : IsPullback ix2 p2 p iy2) :
    Arrow.mk (coprod.map p1 p2) ≅
      Arrow.mk (pullback.snd p (coprod.desc iy1 iy2)) :=
  Arrow.isoMk (f := Arrow.mk (coprod.map p1 p2))
    (g := Arrow.mk (pullback.snd p (coprod.desc iy1 iy2)))
    (coverIso leftPB rightPB) (Iso.refl (Y1 ⨿ Y2)) (by
      change (coverIso leftPB rightPB).hom ≫ pullback.snd p (coprod.desc iy1 iy2) =
        coprod.map p1 p2 ≫ 𝟙 (Y1 ⨿ Y2)
      exact (coverIso_legs leftPB rightPB).2.1.trans (Category.comp_id _).symm)

/-- Both original coproduct injections become their literal native pullback lifts. -/
theorem coverIso_injections {X1 X2 PX Y1 Y2 PY : SSet.{u}}
    {ix1 : X1 ⟶ PX} {ix2 : X2 ⟶ PX} {iy1 : Y1 ⟶ PY} {iy2 : Y2 ⟶ PY}
    {p1 : X1 ⟶ Y1} {p2 : X2 ⟶ Y2} {p : PX ⟶ PY}
    (leftPB : IsPullback ix1 p1 p iy1) (rightPB : IsPullback ix2 p2 p iy2) :
    coprod.inl ≫ (coverIso leftPB rightPB).hom =
      pullback.lift ix1 (p1 ≫ coprod.inl)
        (by simpa only [Category.assoc, coprod.inl_desc] using leftPB.w) ∧
    coprod.inr ≫ (coverIso leftPB rightPB).hom =
      pullback.lift ix2 (p2 ≫ coprod.inr)
        (by simpa only [Category.assoc, coprod.inr_desc] using rightPB.w) := by
  constructor
  · apply pullback.hom_ext <;> simp [Category.assoc, coverIso]
  · apply pullback.hom_ext <;> simp [Category.assoc, coverIso]

end SSet.RezkCompatiblePushout
