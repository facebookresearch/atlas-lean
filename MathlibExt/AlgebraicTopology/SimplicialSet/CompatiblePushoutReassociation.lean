/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SSet.RezkCompatiblePushout

/-- In case b, horizontal pushout pasting retains the original span after
the actual equality ell ≫ r = u0. No weak-colimit argument is used. -/
theorem caseB_pushout {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X1)
    (h : ell ≫ r = u0) :
    IsPushout u0 v0
      (pushout.inl r (pushout.inr v0 ell))
      (pushout.inl v0 ell ≫ pushout.inr r (pushout.inr v0 ell)) := by
  have hpo := (IsPushout.of_hasPushout v0 ell).flip.paste_horiz
    (IsPushout.of_hasPushout r (pushout.inr v0 ell))
  simpa only [h] using hpo

/-- The actual original pushout and the case-b replacement are strictly isomorphic. -/
def caseBIso {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X1)
    (h : ell ≫ r = u0) :
    pushout u0 v0 ≅ pushout r (pushout.inr v0 ell) :=
  (caseB_pushout u0 v0 ell r h).isoPushout.symm

/-- All original forward and inverse injection equations in case b. -/
theorem caseB_iso_legs {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X1)
    (h : ell ≫ r = u0) :
    pushout.inl u0 v0 ≫ (caseBIso u0 v0 ell r h).hom =
        pushout.inl r (pushout.inr v0 ell) ∧
      pushout.inr u0 v0 ≫ (caseBIso u0 v0 ell r h).hom =
        pushout.inl v0 ell ≫ pushout.inr r (pushout.inr v0 ell) ∧
      pushout.inl r (pushout.inr v0 ell) ≫ (caseBIso u0 v0 ell r h).inv =
        pushout.inl u0 v0 ∧
      (pushout.inl v0 ell ≫ pushout.inr r (pushout.inr v0 ell)) ≫
        (caseBIso u0 v0 ell r h).inv = pushout.inr u0 v0 := by
  exact ⟨(caseB_pushout u0 v0 ell r h).inl_isoPushout_inv,
    (caseB_pushout u0 v0 ell r h).inr_isoPushout_inv,
    (caseB_pushout u0 v0 ell r h).inl_isoPushout_hom,
    (caseB_pushout u0 v0 ell r h).inr_isoPushout_hom⟩

/-- In case c, vertical pasting retains v0 via the actual ell ≫ r = v0 law. -/
theorem caseC_pushout {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X2)
    (h : ell ≫ r = v0) :
    IsPushout u0 v0
      (pushout.inl u0 ell ≫ pushout.inl (pushout.inr u0 ell) r)
      (pushout.inr (pushout.inr u0 ell) r) := by
  have hpo := (IsPushout.of_hasPushout u0 ell).paste_vert
    (IsPushout.of_hasPushout (pushout.inr u0 ell) r)
  simpa only [h] using hpo

/-- The actual original pushout and the case-c replacement are strictly isomorphic. -/
def caseCIso {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X2)
    (h : ell ≫ r = v0) :
    pushout u0 v0 ≅ pushout (pushout.inr u0 ell) r :=
  (caseC_pushout u0 v0 ell r h).isoPushout.symm

/-- All original forward and inverse injection equations in case c. -/
theorem caseC_iso_legs {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X2)
    (h : ell ≫ r = v0) :
    pushout.inl u0 v0 ≫ (caseCIso u0 v0 ell r h).hom =
        pushout.inl u0 ell ≫ pushout.inl (pushout.inr u0 ell) r ∧
      pushout.inr u0 v0 ≫ (caseCIso u0 v0 ell r h).hom =
        pushout.inr (pushout.inr u0 ell) r ∧
      (pushout.inl u0 ell ≫ pushout.inl (pushout.inr u0 ell) r) ≫
        (caseCIso u0 v0 ell r h).inv = pushout.inl u0 v0 ∧
      pushout.inr (pushout.inr u0 ell) r ≫ (caseCIso u0 v0 ell r h).inv =
        pushout.inr u0 v0 := by
  exact ⟨(caseC_pushout u0 v0 ell r h).inl_isoPushout_inv,
    (caseC_pushout u0 v0 ell r h).inr_isoPushout_inv,
    (caseC_pushout u0 v0 ell r h).inl_isoPushout_hom,
    (caseC_pushout u0 v0 ell r h).inr_isoPushout_hom⟩

end SSet.RezkCompatiblePushout
