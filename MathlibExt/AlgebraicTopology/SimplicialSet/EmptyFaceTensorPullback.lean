/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Pullback squares over empty simplex faces

Products with the empty face of a standard simplex are initial simplicial sets. Squares whose two left objects are such products are strict pullbacks, and a sharp right map makes their canonical homotopy pullback comparison a weak equivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkEmptyFace
open SharpComparisonDraft RezkCompatiblePushout

/-- Product with the actual empty simplex face is an actual initial object. -/
def emptyTensorInitial (A : SSet.{u}) (n : ℕ) :
    IsInitial (A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u})) :=
  (Subcomplex.isInitialBot (X := (Δ[n] : SSet.{u}))).isInitialObj (tensorLeft A) _

private theorem emptyTensor_obj_false (A : SSet.{u}) (n : ℕ)
    (a : SimplexCategoryᵒᵖ)
    (x : (A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u})).obj a) : False := by
  have h : IsInitial
      ((A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u})).obj a) :=
    (emptyTensorInitial A n).isInitialObj
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj a) _
  let _ : IsEmpty
      ((A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u})).obj a) :=
    (Types.initial_iff_empty _).mp ⟨h⟩
  exact isEmptyElim x

/-- The original square over an empty face is a strict pullback. Its proof
uses the actual empty second coordinate of every cone, not an HC premise. -/
theorem emptyTensor_isPullback {n : ℕ} {A B X Y : SSet.{u}}
    (f : A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (i : A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      B ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}))
    (p : X ⟶ Y)
    (g : B ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ Y) :
    IsPullback f i p g where
  w := (emptyTensorInitial A n).hom_ext _ _
  isLimit' := by
    refine ⟨PullbackCone.IsLimit.mk ((emptyTensorInitial A n).hom_ext _ _)
      (fun s =>
        { app a := ↾fun x => by
            have impossible : False := emptyTensor_obj_false B n a ((s.snd.app a) x)
            exact impossible.elim
          naturality := by
            intro a b h
            apply ConcreteCategory.hom_ext
            intro x
            have impossible : False := emptyTensor_obj_false B n a ((s.snd.app a) x)
            exact impossible.elim }) ?_ ?_ ?_⟩
    · intro s
      apply NatTrans.ext
      funext a
      apply ConcreteCategory.hom_ext
      intro x
      have impossible : False := emptyTensor_obj_false B n a ((s.snd.app a) x)
      exact impossible.elim
    · intro s
      apply NatTrans.ext
      funext a
      apply ConcreteCategory.hom_ext
      intro x
      have impossible : False := emptyTensor_obj_false B n a ((s.snd.app a) x)
      exact impossible.elim
    · intro s m hf hs
      apply NatTrans.ext
      funext a
      apply ConcreteCategory.hom_ext
      intro x
      have impossible : False := emptyTensor_obj_false B n a ((s.snd.app a) x)
      exact impossible.elim

/-- HC for the actual empty-face square follows from its strict pullback
and Sharp of the ORIGINAL right map. No empty/axiom/body exception is used. -/
theorem emptyTensor_hc {n : ℕ} {A B X Y : SSet.{u}}
    (f : A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X)
    (i : A ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      B ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}))
    (p : X ⟶ Y)
    (g : B ⊗ ((⊥ : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ Y) (hp : Sharp p) :
    WeakEquivalence
      (pullback.lift f i ((emptyTensorInitial A n).hom_ext _ _) ≫ comparison p g) :=
  strictSquare_hc (emptyTensor_isPullback f i p g) hp

end SSet.RezkEmptyFace
