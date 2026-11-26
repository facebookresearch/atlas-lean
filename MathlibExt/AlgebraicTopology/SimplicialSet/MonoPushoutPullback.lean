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
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SSet.RezkMonoPushout

/-- Rezk8.4 on the original simplicial sets. A mono top pushout and an
original outer pullback force the bottom square to be a pullback. The middle
horizontal mono is derivable from the top pushout; no Kan or sharpness
hypothesis is used. -/
theorem isPullback_tail {A X A' X' B Y : SSet.{u}}
    {i : A ⟶ X} {p : A ⟶ A'} {f : X ⟶ X'} {i' : A' ⟶ X'}
    {j : A' ⟶ B} {q : X' ⟶ Y} {k : B ⟶ Y}
    [Mono i] [Mono k]
    (top : IsPushout i p f i') (bot : CommSq i' j q k)
    (outer : IsPullback i (p ≫ j) (f ≫ q) k) :
    IsPullback i' j q k := by
  let C := pullback q k
  let c : C ⟶ X' := pullback.fst q k
  let d : C ⟶ B := pullback.snd q k
  let t : A' ⟶ C := pullback.lift i' j bot.w
  have ht_c : t ≫ c = i' := by
    dsimp only [t, c]
    exact pullback.lift_fst _ _ _
  have ht_d : t ≫ d = j := by
    dsimp only [t, d]
    exact pullback.lift_snd _ _ _
  have nativePB : IsPullback c d q k := IsPullback.of_hasPullback q k
  let _ : Mono c := nativePB.mono_fst_of_mono
  have hp_c : (p ≫ t) ≫ c = i ≫ f := by
    rw [Category.assoc, ht_c]
    exact top.w.symm
  have outer' : IsPullback ((p ≫ t) ≫ d) i k (f ≫ q) := by
    simpa only [Category.assoc, ht_d] using outer.flip
  have frontLeft : IsPullback (p ≫ t) i c f :=
    outer'.of_right hp_c nativePB.flip
  have frontRight : IsPullback t (𝟙 A') c i' :=
    IsPullback.of_vert_isIso_mono ⟨by simpa only [Category.id_comp] using ht_c⟩
  have backLeft : IsPullback (𝟙 A) (𝟙 A) i i :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have backRight : IsPullback p (𝟙 A) (𝟙 A') p := IsPullback.id_vert p
  have newTop : IsPushout (𝟙 A) p (p ≫ t) t :=
    (((Adhesive.van_kampen' top.flip).flip)
      (𝟙 A) p (p ≫ t) t (𝟙 A) i (𝟙 A') c
      backLeft backRight frontLeft.toCommSq frontRight.toCommSq
      ⟨by simp⟩).mpr ⟨frontLeft, frontRight⟩
  let _ : IsIso t := newTop.isIso_inr_of_isIso
  have identityFace : IsPullback t j d (𝟙 B) :=
    (IsPullback.of_vert_isIso
      (show CommSq j t (𝟙 B) d from
        ⟨by simpa only [Category.comp_id] using ht_d.symm⟩)).flip
  have recovered := identityFace.paste_horiz nativePB
  simpa only [ht_c, Category.id_comp] using recovered

end SSet.RezkMonoPushout
