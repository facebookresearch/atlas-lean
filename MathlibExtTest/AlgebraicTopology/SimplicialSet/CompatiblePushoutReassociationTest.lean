/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutReassociation
import Mathlib.CategoryTheory.Comma.Arrow

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open SSet.RezkCompatiblePushout
namespace CompatiblePushoutReassociationTest

private theorem horizontal_original_square {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X1)
    (h : ell ≫ r = u0) :
    IsPushout u0 v0 (pushout.inl r (pushout.inr v0 ell))
      (pushout.inl v0 ell ≫ pushout.inr r (pushout.inr v0 ell)) :=
  caseB_pushout u0 v0 ell r h

private theorem vertical_original_square {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X2)
    (h : ell ≫ r = v0) :
    IsPushout u0 v0 (pushout.inl u0 ell ≫ pushout.inl (pushout.inr u0 ell) r)
      (pushout.inr (pushout.inr u0 ell) r) := caseC_pushout u0 v0 ell r h

private theorem horizontal_forward_inverse {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X1)
    (h : ell ≫ r = u0) :
    pushout.inl u0 v0 ≫ (caseBIso u0 v0 ell r h).hom = pushout.inl r (pushout.inr v0 ell) ∧
    pushout.inr u0 v0 ≫ (caseBIso u0 v0 ell r h).hom =
      pushout.inl v0 ell ≫ pushout.inr r (pushout.inr v0 ell) ∧
    pushout.inl r (pushout.inr v0 ell) ≫ (caseBIso u0 v0 ell r h).inv = pushout.inl u0 v0 ∧
    (pushout.inl v0 ell ≫ pushout.inr r (pushout.inr v0 ell)) ≫
      (caseBIso u0 v0 ell r h).inv = pushout.inr u0 v0 := caseB_iso_legs u0 v0 ell r h

private theorem vertical_forward_inverse {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X2)
    (h : ell ≫ r = v0) :
    pushout.inl u0 v0 ≫ (caseCIso u0 v0 ell r h).hom =
      pushout.inl u0 ell ≫ pushout.inl (pushout.inr u0 ell) r ∧
    pushout.inr u0 v0 ≫ (caseCIso u0 v0 ell r h).hom = pushout.inr (pushout.inr u0 ell) r ∧
    (pushout.inl u0 ell ≫ pushout.inl (pushout.inr u0 ell) r) ≫
      (caseCIso u0 v0 ell r h).inv = pushout.inl u0 v0 ∧
    pushout.inr (pushout.inr u0 ell) r ≫ (caseCIso u0 v0 ell r h).inv = pushout.inr u0 v0 :=
  caseC_iso_legs u0 v0 ell r h

private theorem horizontal_roundtrips {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X1)
    (h : ell ≫ r = u0) :
    (caseBIso u0 v0 ell r h).hom ≫ (caseBIso u0 v0 ell r h).inv = 𝟙 _ ∧
      (caseBIso u0 v0 ell r h).inv ≫ (caseBIso u0 v0 ell r h).hom = 𝟙 _ :=
  ⟨(caseBIso u0 v0 ell r h).hom_inv_id, (caseBIso u0 v0 ell r h).inv_hom_id⟩

private theorem vertical_roundtrips {X0 X1 X2 Z0 : SSet.{u}}
    (u0 : X0 ⟶ X1) (v0 : X0 ⟶ X2) (ell : X0 ⟶ Z0) (r : Z0 ⟶ X2)
    (h : ell ≫ r = v0) :
    (caseCIso u0 v0 ell r h).hom ≫ (caseCIso u0 v0 ell r h).inv = 𝟙 _ ∧
      (caseCIso u0 v0 ell r h).inv ≫ (caseCIso u0 v0 ell r h).hom = 𝟙 _ :=
  ⟨(caseCIso u0 v0 ell r h).hom_inv_id, (caseCIso u0 v0 ell r h).inv_hom_id⟩

end CompatiblePushoutReassociationTest
