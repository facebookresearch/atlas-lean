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

public import MathlibExt.SetTheory.InfinitaryCombinatorics.Square
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

open Cardinal Ordinal Set Order

namespace MathlibExtTest.SetTheory.InfinitaryCombinatorics.Square

open MetaMathlibExt

-- Logic 17: $\Square_\kappa$ sequence

/-- A set bounded strictly below `b` by one of its own members does not have `b` as a least
upper bound.  The general fact behind `clauses_vacuous_at_max`. -/

theorem not_isLUB_of_upperBound_lt {α : Type*} [LinearOrder α] {s : Set α} {b m : α}
    (hub : ∀ x ∈ s, x ≤ m) (hmb : m < b) : ¬ IsLUB s b :=
  fun h => absurd (h.2 fun x hx => hub x hx) (not_le.mpr hmb)

/-- The five clauses, spelled out.  `Iff.rfl`, so this is purely an addressing device. -/

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

/-- **Clause 4 needs no `lift`**: `Ordinal.type` of `↥(C a)` and `κ.ord` are both
`Ordinal.{u}`, so the `≤` in clause 4 is well formed with no transport.  Stated as a
comparison rather than as two type ascriptions, because a comparison is what stops
elaborating if the carrier ever moves universe. -/

theorem type_le_ord_no_lift.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    (a : (Order.succ κ).ord.ToType) :
    Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord ∨
      κ.ord < Ordinal.type (α := ↥(C a)) (· < ·) :=
  le_or_gt _ _

/-- Clause 4's cardinality consequence.  The order-type bound is strictly stronger, which is
why the definition states it and not this. -/

theorem card_le_of_type_le.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    {a : (Order.succ κ).ord.ToType}
    (h : Ordinal.type (α := ↥(C a)) (· < ·) ≤ κ.ord) : #(C a) ≤ κ := by
  have h2 := Ordinal.card_le_card h
  rwa [Ordinal.card_type, Cardinal.card_ord] at h2

/-- **Not vacuous**: the constant-`∅` sequence fails, refuted by the cofinality clause alone.
Needs a limit to exist in the carrier, which is exactly what
`isSquareSequence_of_no_succLimit` shows can fail. -/

theorem not_isSquareSequence_const_empty.{u} {κ : Cardinal.{u}}
    (a : (Order.succ κ).ord.ToType) (ha : Order.IsSuccLimit a) :
    ¬ IsSquareSequence κ (fun _ => ∅) := by
  intro h
  obtain ⟨-, hcof, -⟩ := h a ha
  obtain ⟨b, hb⟩ := not_isMin_iff.mp ha.not_isMin
  obtain ⟨c, hc, -⟩ := hcof b hb
  exact hc

/-- **Clause 5 at `b = a` is free**, so quantifying it over all `b` rather than `b < a` adds
no constraint beyond clause 1. -/

theorem coherence_at_self.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    {a : (Order.succ κ).ord.ToType} (h1 : C a ⊆ Set.Iio a) :
    C a = C a ∩ Set.Iio a :=
  (Set.inter_eq_self_of_subset_left h1).symm

/-- **Clauses 3 and 5 bite only at limit points**: if `C a ∩ Set.Iio b` attains a maximum then
`b` is not its least upper bound, so both hypotheses fail and the clauses say nothing. -/

theorem clauses_vacuous_at_max.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    {a b m : (Order.succ κ).ord.ToType}
    (hm : m ∈ C a ∩ Set.Iio b) (hub : ∀ x ∈ C a ∩ Set.Iio b, x ≤ m) :
    ¬ IsLUB (C a ∩ Set.Iio b) b :=
  not_isLUB_of_upperBound_lt hub hm.2

/-- Mathlib's `Order.IsSuccLimit` excludes minimal elements — `Order.IsSuccPrelimit` is the
variant that allows `⊥`.  This is what makes the cofinality clause usable in
`not_isSquareSequence_const_empty`. -/

theorem isSuccLimit_not_isMin.{u} {κ : Cardinal.{u}}
    {a : (Order.succ κ).ord.ToType} (ha : Order.IsSuccLimit a) : ¬ IsMin a := ha.not_isMin

/-- **Degenerate case**: with no successor-limits in the carrier every clause is unreachable
and the predicate holds of every `C`. -/

theorem isSquareSequence_of_no_succLimit.{u} {κ : Cardinal.{u}}
    (C : (Order.succ κ).ord.ToType → Set ((Order.succ κ).ord.ToType))
    (h : ∀ a : (Order.succ κ).ord.ToType, ¬ Order.IsSuccLimit a) :
    IsSquareSequence κ C :=
  fun a ha => absurd ha (h a)

-- Logic 18: $\Square_\kappa$ sequence exists

/-- **Every witness is nontrivial at every limit.**  The cofinality clause forces `C a` to be
nonempty whenever `a` is a successor-limit, so `Square κ` is never satisfied by a degenerate
sequence — in particular not by the constant `∅` one. -/

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

/-- **Degenerate case, and the only way the existential is free.**  On a carrier with no
successor-limits every clause of `IsSquareSequence` sits behind an unreachable hypothesis, so
`Square κ` holds with an arbitrary witness and asserts nothing. -/

theorem square_of_no_succLimit.{u} {κ : Cardinal.{u}}
    (h : ∀ a : (Order.succ κ).ord.ToType, ¬ Order.IsSuccLimit a) : Square κ :=
  ⟨fun _ => ∅, fun a ha => absurd ha (h a)⟩

end MathlibExtTest.SetTheory.InfinitaryCombinatorics.Square

end
