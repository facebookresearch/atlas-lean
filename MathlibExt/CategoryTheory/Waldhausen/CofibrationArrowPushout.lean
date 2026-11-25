/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.ArrowPushout

/-!
# Pushouts in the Waldhausen cofibration-arrow category

A relative cofibration and an arbitrary square determine a selected
componentwise pushout in the full category of cofibration arrows. The apex
arrow is a cofibration and the cobase leg is again relative.

No Waldhausen instance, gluing, cylinder, Stage, or Approximation structure
is installed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

structure CofibrationArrowPushoutPresentation
    {X Y Z : CofibrationArrow C}
    (i : X ⟶ Y) (g : X ⟶ Z) where
  apex : CofibrationArrow C
  inl : Z ⟶ apex
  inr : Y ⟶ apex
  isPushout_left : IsPushout g.left i.left inl.left inr.left
  isPushout_right : IsPushout g.right i.right inl.right inr.right
  inl_relative : IsRelativeCofibration C inl

namespace CofibrationArrowPushoutPresentation

variable {C}
variable {X Y Z : CofibrationArrow C} (i : X ⟶ Y) (g : X ⟶ Z)

noncomputable def ofRelativeCofibration
    (hi : IsRelativeCofibration C i) :
    CofibrationArrowPushoutPresentation C i g := by
  have h : Nonempty (CofibrationArrowPushoutPresentation C i g) := by
    let P := ArrowPushoutPresentation.ofPointwiseCofibration
      ((cofibrationArrowForget C).map i)
      ((cofibrationArrowForget C).map g)
      (hi.pointwise C)
    let zL : Z.left ⟶ P.apex.left := P.inl.left
    let yL : Y.left ⟶ P.apex.left := P.inr.left
    let zR : Z.right ⟶ P.apex.right := P.inl.right
    let yR : Y.right ⟶ P.apex.right := P.inr.right
    have hzLcof : IsCofibration zL := P.inl_cofibration.1
    have hPL : IsPushout g.left i.left zL yL :=
      P.isPushout_left
    have hPR : IsPushout g.right i.right zR yR :=
      P.isPushout_right
    have hPinl :
        zL ≫ P.apex.hom = Z.hom ≫ zR :=
      P.inl.w
    have hPinr :
        yL ≫ P.apex.hom = Y.hom ≫ yR :=
      P.inr.w
    have hg : g.left ≫ Z.hom = X.hom ≫ g.right :=
      g.w
    obtain ⟨_hiLeft, L, pB, pA, d₀, hL, hpB, hpA, hd₀⟩ := hi
    have hZcof : IsCofibration Z.hom := Z.prop
    obtain ⟨R, rPL, rZR, hRraw, _⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
        Z.hom hZcof P.apex.left zL
    have hR : IsPushout Z.hom zL rZR rPL := hRraw.flip
    have hagreeQ :
        X.hom ≫ (g.right ≫ rZR) =
          i.left ≫ (yL ≫ rPL) := by
      calc
        X.hom ≫ (g.right ≫ rZR) =
            (X.hom ≫ g.right) ≫ rZR :=
          (Category.assoc _ _ _).symm
        _ = (g.left ≫ Z.hom) ≫ rZR := by rw [hg]
        _ = g.left ≫ (Z.hom ≫ rZR) :=
          Category.assoc _ _ _
        _ = g.left ≫ (zL ≫ rPL) := by rw [hR.w]
        _ = (g.left ≫ zL) ≫ rPL :=
          (Category.assoc _ _ _).symm
        _ = (i.left ≫ yL) ≫ rPL := by rw [hPL.w]
        _ = i.left ≫ (yL ≫ rPL) :=
          Category.assoc _ _ _
    let q : L ⟶ R :=
      hL.desc (g.right ≫ rZR) (yL ≫ rPL) hagreeQ
    have hpBq : pB ≫ q = g.right ≫ rZR :=
      hL.inl_desc _ _ _
    have hpAq : pA ≫ q = yL ≫ rPL :=
      hL.inr_desc _ _ _
    let d : R ⟶ P.apex.right :=
      hR.desc zR P.apex.hom hPinl.symm
    have hrZR : rZR ≫ d = zR :=
      hR.inl_desc _ _ _
    have hrPL : rPL ≫ d = P.apex.hom :=
      hR.inr_desc _ _ _
    have houterQ :
        IsPushout i.left (X.hom ≫ g.right) (pA ≫ q) rZR := by
      rw [← hg, hpAq]
      exact hPL.flip.paste_vert hRraw
    have hQ : IsPushout pB g.right q rZR :=
      houterQ.of_top hpBq hL.flip
    have hcomm : d₀ ≫ yR = q ≫ d := by
      apply hL.hom_ext
      · calc
          pB ≫ (d₀ ≫ yR) =
              (pB ≫ d₀) ≫ yR :=
            (Category.assoc _ _ _).symm
          _ = i.right ≫ yR := by rw [hpB]
          _ = g.right ≫ zR := hPR.w.symm
          _ = g.right ≫ (rZR ≫ d) := by rw [hrZR]
          _ = (g.right ≫ rZR) ≫ d :=
            (Category.assoc _ _ _).symm
          _ = (pB ≫ q) ≫ d := by rw [hpBq]
          _ = pB ≫ (q ≫ d) := Category.assoc _ _ _
      · calc
          pA ≫ (d₀ ≫ yR) =
              (pA ≫ d₀) ≫ yR :=
            (Category.assoc _ _ _).symm
          _ = Y.hom ≫ yR := by rw [hpA]
          _ = yL ≫ P.apex.hom := hPinr.symm
          _ = yL ≫ (rPL ≫ d) := by rw [hrPL]
          _ = (yL ≫ rPL) ≫ d :=
            (Category.assoc _ _ _).symm
          _ = (pA ≫ q) ≫ d := by rw [hpAq]
          _ = pA ≫ (q ≫ d) := Category.assoc _ _ _
    have houterD :
        IsPushout (pB ≫ d₀) g.right yR (rZR ≫ d) := by
      rw [hpB, hrZR]
      exact hPR.flip
    have hD : IsPushout d₀ q yR d :=
      houterD.of_left hcomm hQ
    have hd : IsCofibration d :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout hD.flip hd₀
    have hrPLcof : IsCofibration rPL :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout hR.flip hZcof
    have hApex : IsCofibration P.apex.hom := by
      rw [← hrPL]
      exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem
        rPL d hrPLcof hd
    let apex : CofibrationArrow C :=
      MorphismProperty.Arrow.mk P.apex.hom hApex
    let inl : Z ⟶ apex :=
      MorphismProperty.Arrow.homMk zL zR hPinl
    let inr : Y ⟶ apex :=
      MorphismProperty.Arrow.homMk yL yR hPinr
    exact ⟨{
      apex := apex
      inl := inl
      inr := inr
      isPushout_left := hPL
      isPushout_right := hPR
      inl_relative := ⟨hzLcof,
        R, rZR, rPL, d, hR, hrZR, hrPL, hd⟩ }⟩
  exact Classical.choice h

theorem isPushout (P : CofibrationArrowPushoutPresentation C i g) :
    IsPushout g i P.inl P.inr := by
  let Q : ArrowPushoutPresentation C
      ((cofibrationArrowForget C).map i)
      ((cofibrationArrowForget C).map g) :=
    { apex := (cofibrationArrowForget C).obj P.apex
      inl := (cofibrationArrowForget C).map P.inl
      inr := (cofibrationArrowForget C).map P.inr
      isPushout_left := P.isPushout_left
      isPushout_right := P.isPushout_right
      inl_cofibration := P.inl_relative.pointwise C }
  apply IsPushout.of_map_of_faithful (cofibrationArrowForget C)
  exact Q.isPushout

end CofibrationArrowPushoutPresentation

end CategoryTheory.Waldhausen
