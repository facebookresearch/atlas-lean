/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing

/-!
# Categorical gluing for the original simplicial pushout maps

Reuse the actual named Joyal model on its designated carrier and
its original categorical weak class and monomorphism cofibrations.
Every object is cofibrant, so the native all-cofibrant properness
theorem and existing proper-span gluing theorem apply. Transport
through the original carrier equivalence gives categorical gluing
for the actual simplicial maps, without a new model record or a
strict higher-homotopy correction premise.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SSet.WalkingAdjunction

attribute [local instance] JoyalSSet.modelCategory

private theorem named_cofibration_iff_mono {A B : JoyalSSet.{u}} (f : A ⟶ B) : Cofibration f ↔ Mono f := by
  rw [cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations f ↔ Mono f
  rw [JoyalSSet.modelCategory_cofibrations]

private theorem named_weak_iff_categorical {A B : SSet.{u}} (f : A ⟶ B) :
    WeakEquivalence (JoyalSSet.ofSSet.map f) ↔ categoricalEquivalences f := by
  rw [weakEquivalence_iff]
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (JoyalSSet.ofSSet.map f) ↔ categoricalEquivalences f
  rw [JoyalSSet.modelCategory_weakEquivalences]
  rfl

private theorem named_all_cofibrant (X : JoyalSSet.{u}) : IsCofibrant X := by
  rcases X with ⟨K⟩
  change IsCofibrant (JoyalSSet.ofSSet.obj K)
  exact (isCofibrant_iff_of_isInitial (JoyalSSet.ofSSet.map (initial.to K))
    (initialIsInitial.isInitialObj JoyalSSet.ofSSet (⊥_ SSet.{u}))).mpr
      ((named_cofibration_iff_mono _).mpr inferInstance)

private local instance namedJoyalLeftProper : IsLeftProper JoyalSSet.{u} :=
  isLeftProper_of_all_objects_cofibrant named_all_cofibrant

/-- A pointwise categorical equivalence of actual pushout spans is categorical on their whole pushouts when the designated original legs are monic. -/
theorem categoricalEquivalences_of_isPushouts
    {A B X P A' B' X' P' : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Mono i] [Mono i']
    (ha : categoricalEquivalences a) (hb : categoricalEquivalences b) (hc : categoricalEquivalences c) :
    categoricalEquivalences d := by
  let _ : Cofibration (JoyalSSet.ofSSet.map i) := named_cofibration_iff_mono _ |>.mpr inferInstance
  let _ : Cofibration (JoyalSSet.ofSSet.map i') := named_cofibration_iff_mono _ |>.mpr inferInstance
  let _ : WeakEquivalence (JoyalSSet.ofSSet.map a) := (named_weak_iff_categorical a).mpr ha
  let _ : WeakEquivalence (JoyalSSet.ofSSet.map b) := (named_weak_iff_categorical b).mpr hb
  let _ : WeakEquivalence (JoyalSSet.ofSSet.map c) := (named_weak_iff_categorical c).mpr hc
  have h : WeakEquivalence (JoyalSSet.ofSSet.map d) :=
    IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst (sq.map JoyalSSet.ofSSet) (sq'.map JoyalSSet.ofSSet)
      (a := JoyalSSet.ofSSet.map a) (b := JoyalSSet.ofSSet.map b)
      (c := JoyalSSet.ofSSet.map c) (d := JoyalSSet.ofSSet.map d)
      (by simpa only [CategoryTheory.Functor.map_comp] using congrArg JoyalSSet.ofSSet.map hi)
      (by simpa only [CategoryTheory.Functor.map_comp] using congrArg JoyalSSet.ofSSet.map hg)
      (by simpa only [CategoryTheory.Functor.map_comp] using congrArg JoyalSSet.ofSSet.map hp)
      (by simpa only [CategoryTheory.Functor.map_comp] using congrArg JoyalSSet.ofSSet.map hq)
  exact (named_weak_iff_categorical d).mp h

end SSet.WalkingAdjunction
