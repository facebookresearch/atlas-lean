/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrow

/-!
# Pointwise pushouts in the Waldhausen arrow category

A pointwise cofibration of arrows and an arbitrary square determine selected
component pushouts, an induced arrow between their apices, and a literal
pushout in `Arrow C`.  The cobase leg is retained as a pointwise cofibration.

This file installs no pushout or Waldhausen instance and makes no relative
cofibration, cylinder, Stage, or Approximation claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- A selected pointwise pushout presentation of two morphisms in `Arrow C`.
The cobase leg `inl` starts at `Z`; `inr` starts at `Y`. -/
structure ArrowPushoutPresentation {X Y Z : Arrow C}
    (i : X ⟶ Y) (g : X ⟶ Z) where
  apex : Arrow C
  inl : Z ⟶ apex
  inr : Y ⟶ apex
  isPushout_left : IsPushout g.left i.left inl.left inr.left
  isPushout_right : IsPushout g.right i.right inl.right inr.right
  inl_cofibration : arrowCofibrations C inl

namespace ArrowPushoutPresentation

variable {C}
variable {X Y Z : Arrow C} (i : X ⟶ Y) (g : X ⟶ Z)

/-- Select a pointwise arrow pushout from the local Waldhausen pushout
axioms. -/
noncomputable def ofPointwiseCofibration
    (hi : arrowCofibrations C i) :
    ArrowPushoutPresentation C i g := by
  have h : Nonempty (ArrowPushoutPresentation C i g) := by
    obtain ⟨PL, inlZL, inrYL, hPL, hinlZL⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
        i.left hi.1 Z.left g.left
    obtain ⟨PR, inlZR, inrYR, hPR, hinlZR⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
        i.right hi.2 Z.right g.right
    have hagree :
        g.left ≫ (Z.hom ≫ inlZR) =
          i.left ≫ (Y.hom ≫ inrYR) := by
      calc
        g.left ≫ (Z.hom ≫ inlZR) =
            (g.left ≫ Z.hom) ≫ inlZR :=
          (Category.assoc _ _ _).symm
        _ = (X.hom ≫ g.right) ≫ inlZR := by rw [g.w]
        _ = X.hom ≫ (g.right ≫ inlZR) :=
          Category.assoc _ _ _
        _ = X.hom ≫ (i.right ≫ inrYR) := by rw [hPR.w]
        _ = (X.hom ≫ i.right) ≫ inrYR :=
          (Category.assoc _ _ _).symm
        _ = (i.left ≫ Y.hom) ≫ inrYR := by rw [i.w]
        _ = i.left ≫ (Y.hom ≫ inrYR) :=
          Category.assoc _ _ _
    let apexHom : PL ⟶ PR :=
      hPL.desc (Z.hom ≫ inlZR) (Y.hom ≫ inrYR) hagree
    let apex : Arrow C := Arrow.mk apexHom
    let inl : Z ⟶ apex := Arrow.homMk inlZL inlZR (by
      dsimp only [apex, apexHom]
      exact hPL.inl_desc _ _ _)
    let inr : Y ⟶ apex := Arrow.homMk inrYL inrYR (by
      dsimp only [apex, apexHom]
      exact hPL.inr_desc _ _ _)
    exact ⟨{
      apex := apex
      inl := inl
      inr := inr
      isPushout_left := hPL
      isPushout_right := hPR
      inl_cofibration := ⟨hinlZL, hinlZR⟩ }⟩
  exact Classical.choice h

/-- The selected component pushouts satisfy the literal pushout universal
property in `Arrow C`. -/
theorem isPushout (P : ArrowPushoutPresentation C i g) :
    IsPushout g i P.inl P.inr := by
  refine IsPushout.mk' ?_ ?_ ?_
  · apply Arrow.hom_ext
    · simpa only [Arrow.comp_left] using P.isPushout_left.w
    · simpa only [Arrow.comp_right] using P.isPushout_right.w
  · intro T φ φ' hZ hY
    have hZl : P.inl.left ≫ φ.left = P.inl.left ≫ φ'.left := by
      simpa only [Arrow.comp_left] using congrArg Arrow.Hom.left hZ
    have hYl : P.inr.left ≫ φ.left = P.inr.left ≫ φ'.left := by
      simpa only [Arrow.comp_left] using congrArg Arrow.Hom.left hY
    have hZr : P.inl.right ≫ φ.right = P.inl.right ≫ φ'.right := by
      simpa only [Arrow.comp_right] using congrArg Arrow.Hom.right hZ
    have hYr : P.inr.right ≫ φ.right = P.inr.right ≫ φ'.right := by
      simpa only [Arrow.comp_right] using congrArg Arrow.Hom.right hY
    apply Arrow.hom_ext
    · apply P.isPushout_left.hom_ext
      · exact hZl
      · exact hYl
    · apply P.isPushout_right.hom_ext
      · exact hZr
      · exact hYr
  · intro T a b hab
    have habL : g.left ≫ a.left = i.left ≫ b.left := by
      simpa only [Arrow.comp_left] using congrArg Arrow.Hom.left hab
    have habR : g.right ≫ a.right = i.right ≫ b.right := by
      simpa only [Arrow.comp_right] using congrArg Arrow.Hom.right hab
    let l : P.apex.left ⟶ T.left :=
      P.isPushout_left.desc a.left b.left habL
    let r : P.apex.right ⟶ T.right :=
      P.isPushout_right.desc a.right b.right habR
    have hlr : l ≫ T.hom = P.apex.hom ≫ r := by
      apply P.isPushout_left.hom_ext
      · dsimp only [l, r]
        calc
          P.inl.left ≫ (P.isPushout_left.desc a.left b.left habL ≫ T.hom) =
              (P.inl.left ≫ P.isPushout_left.desc a.left b.left habL) ≫
                T.hom := (Category.assoc _ _ _).symm
          _ = a.left ≫ T.hom := by rw [P.isPushout_left.inl_desc]
          _ = Z.hom ≫ a.right := a.w
          _ = Z.hom ≫
              (P.inl.right ≫ P.isPushout_right.desc a.right b.right habR) := by
            rw [P.isPushout_right.inl_desc]
          _ = (Z.hom ≫ P.inl.right) ≫
              P.isPushout_right.desc a.right b.right habR :=
            (Category.assoc _ _ _).symm
          _ = (P.inl.left ≫ P.apex.hom) ≫
              P.isPushout_right.desc a.right b.right habR := by rw [P.inl.w]
          _ = P.inl.left ≫
              (P.apex.hom ≫ P.isPushout_right.desc a.right b.right habR) :=
            Category.assoc _ _ _
      · dsimp only [l, r]
        calc
          P.inr.left ≫ (P.isPushout_left.desc a.left b.left habL ≫ T.hom) =
              (P.inr.left ≫ P.isPushout_left.desc a.left b.left habL) ≫
                T.hom := (Category.assoc _ _ _).symm
          _ = b.left ≫ T.hom := by rw [P.isPushout_left.inr_desc]
          _ = Y.hom ≫ b.right := b.w
          _ = Y.hom ≫
              (P.inr.right ≫ P.isPushout_right.desc a.right b.right habR) := by
            rw [P.isPushout_right.inr_desc]
          _ = (Y.hom ≫ P.inr.right) ≫
              P.isPushout_right.desc a.right b.right habR :=
            (Category.assoc _ _ _).symm
          _ = (P.inr.left ≫ P.apex.hom) ≫
              P.isPushout_right.desc a.right b.right habR := by rw [P.inr.w]
          _ = P.inr.left ≫
              (P.apex.hom ≫ P.isPushout_right.desc a.right b.right habR) :=
            Category.assoc _ _ _
    let d : P.apex ⟶ T := Arrow.homMk l r hlr
    refine ⟨d, ?_, ?_⟩
    · apply Arrow.hom_ext
      · change P.inl.left ≫ l = a.left
        dsimp only [l]
        exact P.isPushout_left.inl_desc a.left b.left habL
      · change P.inl.right ≫ r = a.right
        dsimp only [r]
        exact P.isPushout_right.inl_desc a.right b.right habR
    · apply Arrow.hom_ext
      · change P.inr.left ≫ l = b.left
        dsimp only [l]
        exact P.isPushout_left.inr_desc a.left b.left habL
      · change P.inr.right ≫ r = b.right
        dsimp only [r]
        exact P.isPushout_right.inr_desc a.right b.right habR

end ArrowPushoutPresentation

end CategoryTheory.Waldhausen

end
