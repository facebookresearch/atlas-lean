/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Whole categorical arrow readback under actual endpoint equalities

Supplied object equalities retype entire arrows before a faithful
functor reflects their image equality. An actual inverse-composition
functor equation similarly retains each given source arrow literally.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe uX vX uY vY

open CategoryTheory

namespace CategoryTheory.Functor

/-- A whole functor equality retains the image of the same supplied arrow. -/
theorem map_whole_heq {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {F G : X ⥤ Y} (h : F = G) {a b : X} (η : a ⟶ b) : HEq (F.map η) (G.map η) := by
  cases h
  rfl

/-- Independent source and target equalities preserve the entire given mapped arrow. -/
theorem map_retyped_heq {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (F : X ⥤ Y) {a b a' b' : X} (ha : a = a') (hb : b = b')
    (η : a ⟶ b) (θ : a' ⟶ b') (h : HEq η θ) : HEq (F.map η) (F.map θ) := by
  cases ha
  cases hb
  cases eq_of_heq h
  rfl

/-- A faithful actual functor reflects the same whole arrow after the given object transports. -/
theorem reflect_retyped_heq {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (F : X ⥤ Y) [F.Faithful] {a b a' b' : X} (ha : a = a') (hb : b = b')
    (η : a ⟶ b) (θ : a' ⟶ b') (h : HEq (F.map η) (F.map θ)) : HEq η θ := by
  cases ha
  cases hb
  exact heq_of_eq (F.map_injective (eq_of_heq h))

/-- The actual whole inverse-composition equation recovers the given source arrow. -/
theorem inverse_comp_map_heq {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    (F : X ⥤ Y) (G : Y ⥤ X) (h : G ⋙ F = 𝟭 Y) {a b : Y} (η : a ⟶ b) :
    HEq (F.map (G.map η)) η :=
  map_whole_heq h η

end CategoryTheory.Functor
