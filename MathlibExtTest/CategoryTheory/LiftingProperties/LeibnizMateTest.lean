/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.LiftingProperties.LeibnizMate

/-!
# Tests for Leibniz adjunctions from mate transformations
-/

set_option autoImplicit false
noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ C}

example {f g g' : Arrow C} (sq : f ⟶ g) (e : g ≅ g') :
    Arrow.LiftStruct sq ≃ Arrow.LiftStruct (sq ≫ e.hom) :=
  Arrow.liftStructPostcompIsoEquiv sq e

namespace NatTrans

example (α : F₀ ⟶ F₁) [HasPushouts D] (u : Arrow C) :
    ((leibnizPushout α).obj u).hom =
      pushout.desc (F₁.map u.hom) (α.app u.right) (by simp) := by
  rfl

example (β : G₁ ⟶ G₀) [HasPullbacks C] (p : Arrow D) :
    ((leibnizPullback β).obj p).hom =
      pullback.lift (β.app p.left) (G₁.map p.hom) (by simp) := by
  rfl

end NatTrans

namespace Adjunction

variable (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
  [HasPushouts D] [HasPullbacks C]

example : NatTrans.leibnizPushout α ⊣
    NatTrans.leibnizPullback (conjugateEquiv adj₁ adj₀ α) :=
  leibnizMateAdjunction adj₀ adj₁ α

example (u : Arrow C) (p : Arrow D) :
    leibnizMateArrowHomEquiv adj₀ adj₁ α u p =
      (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u p := by
  simp

example {A B : C} {u : A ⟶ B} {X Y : D} {p : X ⟶ Y}
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p) :
    HasLiftingProperty sqL.ι p ↔ HasLiftingProperty u sqR.π :=
  leibnizMate_hasLiftingProperty_iff_of adj₀ adj₁ α sqL sqR

example {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq).left =
      adj₁.homEquiv _ _ (sqL.inl ≫ sq.left) :=
  leibnizMateArrowHomEquivOf_apply_left adj₀ adj₁ α u p sqL sqR sq

example {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq).right ≫ sqR.fst =
      adj₀.homEquiv _ _ (sqL.inr ≫ sq.left) :=
  leibnizMateArrowHomEquivOf_apply_right_fst
    adj₀ adj₁ α u p sqL sqR sq

example {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq).right ≫ sqR.snd =
      adj₁.homEquiv _ _ sq.right :=
  leibnizMateArrowHomEquivOf_apply_right_snd
    adj₀ adj₁ α u p sqL sqR sq

example {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sq : Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (parallelPair α α) WalkingParallelPairHom.left u).ι ⟶ Arrow.mk p) :
    leibnizMateArrowHomEquivOf adj₀ adj₁ α u p
        (Functor.PushoutObjObj.ofHasPushout
          (parallelPair α α) WalkingParallelPairHom.left u)
        (Functor.PullbackObjObj.ofHasPullback
          (walkingParallelPairOp.leftOp ⋙
            parallelPair (conjugateEquiv adj₁ adj₀ α)
              (conjugateEquiv adj₁ adj₀ α))
          WalkingParallelPairHom.left p) sq =
      leibnizMateArrowHomEquiv adj₀ adj₁ α (Arrow.mk u) (Arrow.mk p) sq :=
  leibnizMateArrowHomEquivOf_canonical_apply adj₀ adj₁ α u p sq

example {u' u : Arrow C} (i : u' ⟶ u) (p : Arrow D)
    (sq : (NatTrans.leibnizPushout α).obj u ⟶ p) :
    (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u' p
        ((NatTrans.leibnizPushout α).map i ≫ sq) =
      i ≫ (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u p sq := by
  exact (leibnizMateAdjunction adj₀ adj₁ α).homEquiv_naturality_left i sq

example (u : Arrow C) {p p' : Arrow D} (sq :
    (NatTrans.leibnizPushout α).obj u ⟶ p) (k : p ⟶ p') :
    (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u p' (sq ≫ k) =
      (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u p sq ≫
        (NatTrans.leibnizPullback (conjugateEquiv adj₁ adj₀ α)).map k := by
  exact (leibnizMateAdjunction adj₀ adj₁ α).homEquiv_naturality_right sq k

example {u : Arrow C} {p : Arrow D}
    (sq : (NatTrans.leibnizPushout α).obj u ⟶ p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (leibnizMateArrowHomEquiv adj₀ adj₁ α u p sq) :=
  leibnizMateLiftStructEquiv adj₀ adj₁ α sq

example (u : Arrow C) (p : Arrow D) :
    HasLiftingProperty ((NatTrans.leibnizPushout α).obj u).hom p.hom ↔
      HasLiftingProperty u.hom
        ((NatTrans.leibnizPullback
          (conjugateEquiv adj₁ adj₀ α)).obj p).hom :=
  leibnizMate_hasLiftingProperty_iff adj₀ adj₁ α u p

end Adjunction

end CategoryTheory
