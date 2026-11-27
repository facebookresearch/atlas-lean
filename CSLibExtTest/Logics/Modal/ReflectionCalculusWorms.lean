/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Modal.ReflectionCalculusWorms

/-! # Tests for the ordinal assignment of worms -/

namespace Cslib.Modal.RC.ReflectionCalculusWormsTests

/-- Any map as in `exists_wormOrdinal` sends the empty worm `⊤` to `0`: some worm has value `0`,
it would lie below `⊤` otherwise, and `⊤` proves the consistency of no worm (one world, no
accessibility). -/
private theorem nil_eq_zero (o : List ℕ → Ordinal.{0})
    (hlt : ∀ α β, WormLt (Atom := Empty) α β ↔ o α < o β)
    (hrange : Set.range o = Set.Iio (Ordinal.epsilon 0)) : o [] = 0 := by
  by_contra h
  obtain ⟨α, hα⟩ : (0 : Ordinal) ∈ Set.range o := by
    rw [hrange]
    exact Ordinal.epsilon_pos 0
  have hR : IsFrame (fun (_ : ℕ) (_ _ : Unit) ↦ False) :=
    ⟨fun h _ ↦ h.elim, fun _ h _ ↦ h.elim, fun _ h ↦ h.elim⟩
  have hwl := (hlt α []).2 (hα ▸ pos_iff_ne_zero.2 h)
  obtain ⟨_, h', _⟩ := Derives.sound hR (fun _ _ ↦ True) hwl () trivial
  exact h'

/-- The theorem's map gives `⊤` the value `0` and the RC-equivalent worms `1 0` and `1` the same
value; it puts `0 0` below `1`, and `1` below `ε₀`. -/
example : ∃ o : List ℕ → Ordinal.{0},
    o [] = 0 ∧ o [1, 0] = o [1] ∧ o [0, 0] < o [1] ∧ o [1] < Ordinal.epsilon 0 := by
  obtain ⟨o, heq, hlt, hrange⟩ := exists_wormOrdinal
  refine ⟨o, nil_eq_zero o hlt hrange, (heq _ _).2 ⟨.dia_mono 1 (.top _), ?_⟩,
    (hlt _ _).1 (WormLt.replicate_zero_one 2), ?_⟩
  · exact (Derives.and_intro (.refl _) (.monotone Nat.one_pos _)).trans
      ((Derives.dia_and Nat.one_pos _ _).trans (.dia_mono 1 (.and_right _ _)))
  · rw [← Set.mem_Iio, ← hrange]
    exact ⟨[1], rfl⟩

/-- No worm proves its own consistency: `<₀` is irreflexive. -/
example (α : List ℕ) : ¬WormLt (Atom := Empty) α α := by
  obtain ⟨o, -, hlt, -⟩ := exists_wormOrdinal
  exact fun h ↦ lt_irrefl _ ((hlt α α).1 h)

/-- Up to RC-equivalence, `<₀` is a strict linear order on worms. -/
example (α β : List ℕ) :
    WormLt (Atom := Empty) α β ∨
      (Derives (worm α : Formula Empty) (worm β) ∧ Derives (worm β : Formula Empty) (worm α)) ∨
      WormLt (Atom := Empty) β α := by
  obtain ⟨o, heq, hlt, -⟩ := exists_wormOrdinal
  rcases lt_trichotomy (o α) (o β) with h | h | h
  · exact .inl ((hlt α β).2 h)
  · exact .inr (.inl ((heq α β).1 h))
  · exact .inr (.inr ((hlt β α).2 h))

/-- `<₀` is well-founded on worms. -/
example : WellFounded (WormLt (Atom := Empty)) := by
  obtain ⟨o, -, hlt, -⟩ := exists_wormOrdinal
  exact Subrelation.wf (fun {α β} h ↦ (hlt α β).1 h) (InvImage.wf o wellFounded_lt)

/-- Every ordinal below `ε₀` is the value of a worm; for instance `ω ^ ω` is. -/
example : ∃ o : List ℕ → Ordinal.{0}, ∃ α, o α = Ordinal.omega0 ^ Ordinal.omega0 := by
  obtain ⟨o, -, -, hrange⟩ := exists_wormOrdinal
  have h : Ordinal.omega0 ^ Ordinal.omega0 ∈ Set.range o := by
    rw [hrange, Set.mem_Iio, ← Ordinal.omega0_opow_epsilon 0]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (Ordinal.omega0_lt_epsilon 0)
  exact ⟨o, h⟩

end Cslib.Modal.RC.ReflectionCalculusWormsTests
