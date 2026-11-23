/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Existing pushout homotopy descent on an actual pushout cocone

The original arbitrary pushout apex is transported to the stock pushout
by its canonical IsPushout Iso. The existing jointly continuous quotient
homotopy is reused once; its two original leg equations are retained.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat.Homotopy

/-- Compatible actual leg homotopies descend to an arbitrary actual
pushout cocone, using the existing stock pushout homotopy. -/
public def descOfIsPushout
    {S A B P Y : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (sq : IsPushout f g a b) {a₀ a₁ : A ⟶ Y} {b₀ b₁ : B ⟶ Y}
    (HA : TopCat.Homotopy a₀ a₁) (HB : TopCat.Homotopy b₀ b₁)
    (h₀ : f ≫ a₀ = g ≫ b₀) (h₁ : f ≫ a₁ = g ≫ b₁)
    (h : ∀ t : unitInterval, ∀ s : S, HA (t, f s) = HB (t, g s)) :
    TopCat.Homotopy (sq.desc a₀ b₀ h₀) (sq.desc a₁ b₁ h₁) := by
  let e := sq.isoPushout
  let H := pushoutDesc HA HB h₀ h₁ h
  let K := H.compContinuousMap e.hom.hom
  have hs₀ : e.hom ≫ pushout.desc a₀ b₀ h₀ = sq.desc a₀ b₀ h₀ := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.inl_isoPushout_hom, pushout.inl_desc, sq.inl_desc]
    · rw [← Category.assoc, sq.inr_isoPushout_hom, pushout.inr_desc, sq.inr_desc]
  have hs₁ : e.hom ≫ pushout.desc a₁ b₁ h₁ = sq.desc a₁ b₁ h₁ := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.inl_isoPushout_hom, pushout.inl_desc, sq.inl_desc]
    · rw [← Category.assoc, sq.inr_isoPushout_hom, pushout.inr_desc, sq.inr_desc]
  exact K.cast
    ((TopCat.hom_comp e.hom (pushout.desc a₀ b₀ h₀)).symm.trans
      (congrArg (fun k : P ⟶ Y => k.hom) hs₀))
    ((TopCat.hom_comp e.hom (pushout.desc a₁ b₁ h₁)).symm.trans
      (congrArg (fun k : P ⟶ Y => k.hom) hs₁))

public theorem descOfIsPushout_apply_inl
    {S A B P Y : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (sq : IsPushout f g a b) {a₀ a₁ : A ⟶ Y} {b₀ b₁ : B ⟶ Y}
    (HA : TopCat.Homotopy a₀ a₁) (HB : TopCat.Homotopy b₀ b₁)
    (h₀ : f ≫ a₀ = g ≫ b₀) (h₁ : f ≫ a₁ = g ≫ b₁)
    (h : ∀ t : unitInterval, ∀ s : S, HA (t, f s) = HB (t, g s))
    (t : unitInterval) (x : A) :
    descOfIsPushout sq HA HB h₀ h₁ h (t, a x) = HA (t, x) := by
  simp only [descOfIsPushout, ContinuousMap.Homotopy.cast_apply,
    ContinuousMap.Homotopy.compContinuousMap_apply]
  have hx := ConcreteCategory.congr_hom sq.inl_isoPushout_hom x
  change (sq.isoPushout.hom) (a x) = pushout.inl f g x at hx
  rw [hx, pushoutDesc_apply_inl]

public theorem descOfIsPushout_apply_inr
    {S A B P Y : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {a : A ⟶ P} {b : B ⟶ P}
    (sq : IsPushout f g a b) {a₀ a₁ : A ⟶ Y} {b₀ b₁ : B ⟶ Y}
    (HA : TopCat.Homotopy a₀ a₁) (HB : TopCat.Homotopy b₀ b₁)
    (h₀ : f ≫ a₀ = g ≫ b₀) (h₁ : f ≫ a₁ = g ≫ b₁)
    (h : ∀ t : unitInterval, ∀ s : S, HA (t, f s) = HB (t, g s))
    (t : unitInterval) (x : B) :
    descOfIsPushout sq HA HB h₀ h₁ h (t, b x) = HB (t, x) := by
  simp only [descOfIsPushout, ContinuousMap.Homotopy.cast_apply,
    ContinuousMap.Homotopy.compContinuousMap_apply]
  have hx := ConcreteCategory.congr_hom sq.inr_isoPushout_hom x
  change (sq.isoPushout.hom) (b x) = pushout.inr f g x at hx
  rw [hx, pushoutDesc_apply_inr]

end TopCat.Homotopy

end
