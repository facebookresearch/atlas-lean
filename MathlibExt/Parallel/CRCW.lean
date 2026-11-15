/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic.NormNum

/-!
# CRCW PRAM write resolution

In one CRCW PRAM step, all processors write to a shared cell
simultaneously. This module proves the one-step resolution
rules: under the max rule the cell takes the maximum written
value (one of the written values), and under the OR rule the
cell is `true` exactly when some processor writes `true`. The
EREW simulation with logarithmic slowdown is not formalized
here.
-/

@[expose] public section

/-- One-step CRCW PRAM write resolution for a shared cell
(core of DPA-26): all processors write simultaneously; under
the max (priority) rule the cell takes the maximum written
value, under the OR rule it records whether anyone wrote 1. -/
noncomputable def crcwMax {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  Finset.sup Finset.univ w

/-- The max-rule cell value is one of the written values (when
there is at least one processor). -/
theorem crcwMax_mem {n : ℕ} (hn : 0 < n) (w : Fin n → ℕ) :
    ∃ i, crcwMax w = w i := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ w
  exact ⟨i, hi⟩

/-- A processor's value is at most the cell value. -/
theorem le_crcwMax {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    w i ≤ crcwMax w := by
  exact Finset.le_sup (s := Finset.univ) (f := w) (Finset.mem_univ i)

/-- OR rule: the cell is `true` iff some processor writes
`true`. -/
theorem crcwOr_iff {n : ℕ} (w : Fin n → Bool) :
    (Finset.sup Finset.univ w = true) ↔ ∃ i, w i = true := by
  constructor
  · intro h
    by_contra hc
    have hall : ∀ i, w i ≠ true := fun i hi => hc ⟨i, hi⟩
    have hbot := (Finset.sup_eq_bot_iff w Finset.univ).mpr (fun s _ => by
      cases hws : w s
      · rfl
      · exact absurd hws (hall s))
    rw [h] at hbot
    exact absurd hbot (by decide)
  · rintro ⟨i, hi⟩
    have hle : w i ≤ Finset.sup Finset.univ w :=
      Finset.le_sup (Finset.mem_univ i)
    rw [hi] at hle
    exact le_antisymm le_top hle

end
