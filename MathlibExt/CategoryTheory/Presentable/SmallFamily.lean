/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua
module
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# One actual presentability rank for a small family

For a small family of genuinely presentable objects, bound the original
rank ordinals by one regular cardinal. Monotonicity then proves that all
original objects are presentable at that rank. This retains independent
object, Hom and working universes and does not replace source presentability
by smallness of the family labels.
-/

@[expose] public section
noncomputable section
universe w v u t
open CategoryTheory Opposite

namespace CategoryTheory

/-- A small family of actual presentable objects has a common regular native rank. -/
theorem exists_cardinalPresentable_small_family {C : Type u} [Category.{v} C]
    {ι : Type t} [Small.{w} ι] (A : ι → C) [∀ i, IsPresentable.{w} (A i)] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), ∀ i, IsCardinalPresentable (A i) κ := by
  choose κ hκ hA using fun i => Functor.IsAccessible.exists_cardinal (coyoneda.obj (op (A i)))
  obtain ⟨κ', hκ', h⟩ := HasCardinalLT.exists_regular_cardinal_forall (fun i => (κ i).ord.ToType)
  let _ : Fact κ'.IsRegular := ⟨hκ'⟩
  refine ⟨κ', inferInstance, fun i => ?_⟩
  let _ : Fact (κ i).IsRegular := hκ i
  let _ : IsCardinalPresentable (A i) (κ i) := hA i
  have hle : κ i ≤ κ' := by
    have hi := h i
    simp only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType, Cardinal.card_ord] at hi
    exact hi.le
  exact isCardinalPresentable_of_le (A i) hle

end CategoryTheory
