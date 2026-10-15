/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 17, Logic 18
-- Proposed path (advisory metadata only, not a review instruction).

open Cardinal Ordinal Set Order

-- Logic 17: $\Square_\kappa$ sequence
def IsSquareSequence.{u} (κ : Cardinal.{u})
      (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType)) : Prop :=
    ∀ a : (Order.succ κ).ord.ToType, Order.IsSuccLimit a →
      (C a ⊆ Set.Iio a) ∧
      (∀ b < a, ∃ c ∈ C a, b < c) ∧
      (∀ b < a, (C a ∩ Set.Iio b).Nonempty → IsLUB (C a ∩ Set.Iio b) b → b ∈ C a) ∧
      Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord ∧
      (∀ b, (C a ∩ Set.Iio b).Nonempty → IsLUB (C a ∩ Set.Iio b) b →
        C b = C a ∩ Set.Iio b)

theorem not_isLUB_of_upperBound_lt {α : Type*} [LinearOrder α] {s : Set α} {b m : α}
    (hub : ∀ x ∈ s, x ≤ m) (hmb : m < b) : ¬ IsLUB s b :=
  fun h => absurd (h.2 fun x hx => hub x hx) (not_le.mpr hmb)

theorem isSquareSequence_iff.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType)) :
    IsSquareSequence κ C ↔
      ∀ a : (Order.succ κ).ord.ToType, Order.IsSuccLimit a →
        (C a ⊆ Set.Iio a) ∧
        (∀ b < a, ∃ c ∈ C a, b < c) ∧
        (∀ b < a, (C a ∩ Set.Iio b).Nonempty → IsLUB (C a ∩ Set.Iio b) b → b ∈ C a) ∧
        Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord ∧
        (∀ b, (C a ∩ Set.Iio b).Nonempty → IsLUB (C a ∩ Set.Iio b) b →
          C b = C a ∩ Set.Iio b) :=
  Iff.rfl

theorem type_le_ord_no_lift.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    (a : (Order.succ κ).ord.ToType) :
    Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord ∨
      κ.ord < Ordinal.type (α := ↥(C a)) (· < ·) :=
  le_or_gt _ _

theorem card_le_of_type_le.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    {a : (Order.succ κ).ord.ToType}
    (h : Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord) : #(C a) ≤ κ := by
  have h2 := Ordinal.card_le_card h
  rwa [Ordinal.card_type, Cardinal.card_ord] at h2

theorem not_isSquareSequence_const_empty.{u} {κ : Cardinal.{u}}
    (a : (Order.succ κ).ord.ToType) (ha : Order.IsSuccLimit a) :
    ¬ IsSquareSequence κ (fun _ => ∅) := by
  intro h
  obtain ⟨-, hcof, -⟩ := h a ha
  obtain ⟨b, hb⟩ := not_isMin_iff.mp ha.not_isMin
  obtain ⟨c, hc, -⟩ := hcof b hb
  exact hc

theorem coherence_at_self.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    {a : (Order.succ κ).ord.ToType} (h1 : C a ⊆ Set.Iio a) :
    C a = C a ∩ Set.Iio a :=
  (Set.inter_eq_self_of_subset_left h1).symm

theorem clauses_vacuous_at_max.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    {a b m : (Order.succ κ).ord.ToType}
    (hm : m ∈ C a ∩ Set.Iio b) (hub : ∀ x ∈ C a ∩ Set.Iio b, x ≤ m) :
    ¬ IsLUB (C a ∩ Set.Iio b) b :=
  not_isLUB_of_upperBound_lt hub hm.2

theorem isSuccLimit_not_isMin.{u} {κ : Cardinal.{u}}
    {a : (Order.succ κ).ord.ToType} (ha : Order.IsSuccLimit a) : ¬ IsMin a := ha.not_isMin

theorem isSquareSequence_of_no_succLimit.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    (h : ∀ a : (Order.succ κ).ord.ToType, ¬ Order.IsSuccLimit a) :
    IsSquareSequence κ C :=
  fun a ha => absurd ha (h a)

-- Logic 18: $\Square_\kappa$ sequence exists
def Square.{u} (κ : Cardinal.{u}) : Prop :=
    ∃ C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType), IsSquareSequence κ C

theorem Square.nonempty_at_limit.{u} {κ : Cardinal.{u}} (h : Square κ)
    (a : (Order.succ κ).ord.ToType) (ha : Order.IsSuccLimit a) :
    ∃ C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType),
      IsSquareSequence κ C ∧ (C a).Nonempty := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, hC, ?_⟩
  obtain ⟨-, hcof, -⟩ := hC a ha
  obtain ⟨b, hb⟩ := not_isMin_iff.mp ha.not_isMin
  obtain ⟨c, hc, -⟩ := hcof b hb
  exact ⟨c, hc⟩

theorem square_of_no_succLimit.{u} {κ : Cardinal.{u}}
    (h : ∀ a : (Order.succ κ).ord.ToType, ¬ Order.IsSuccLimit a) : Square κ :=
  ⟨fun _ => ∅, fun a ha => absurd ha (h a)⟩

end
