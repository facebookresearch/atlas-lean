/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Retyping arrows across equal endpoints

A functor preserves heterogeneous equality between two retyped arrows. A faithful functor
also reflects it when equalities of the source and target objects are given.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe uX vX uY vY

open CategoryTheory

namespace CategoryTheory.Functor

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

end CategoryTheory.Functor
