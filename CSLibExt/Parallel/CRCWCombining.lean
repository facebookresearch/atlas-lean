/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

/-!
# Combining CRCW write resolution: maximum and OR

In a combining CRCW PRAM, concurrent writes to one shared cell are resolved by combining
the written values. For the values `w : Fin n → _` written by `n` processors, `crcwMax w`
resolves natural-number writes by the maximum rule and `crcwOr w` resolves Boolean writes
by the OR rule. Both are finite suprema over `Finset.univ` and evaluate by computation.

These rules differ from the Priority CRCW rule of `Cslib.Parallel.PRAM.stepCRCW`
(`CSLibExt.Parallel.PRAM`), where the least-index writer wins: for the writes `0, 3`,
priority stores processor `0`'s value `0`, while the maximum rule stores `3`.

With no processors (`n = 0`) the maximum is `0`, the supremum of the empty family in `ℕ`,
and the OR is `false`. These operators resolve only the values actually written; in a PRAM
step, a cell that no processor writes keeps its old value
(`Cslib.Parallel.PRAM.stepCRCW_of_no_writer`).

## Main results

* `Cslib.Parallel.PRAM.crcwMax_mem`: with at least one processor, the maximum is one of the
  written values.
* `Cslib.Parallel.PRAM.le_crcwMax`: every written value is at most the maximum.
* `Cslib.Parallel.PRAM.crcwOr_iff`: the OR is `true` iff some processor writes `true`.
-/

@[expose] public section

namespace Cslib.Parallel.PRAM

/-- Maximum-rule write resolution: the cell takes the largest of the values `w i` written by
the `n` processors (`0` when `n = 0`). -/
def crcwMax {n : ℕ} (w : Fin n → ℕ) : ℕ :=
  Finset.univ.sup w

/-- OR-rule write resolution: the supremum of the Boolean values `w i` written by the `n`
processors (`false` when `n = 0`); see `crcwOr_iff`. -/
def crcwOr {n : ℕ} (w : Fin n → Bool) : Bool :=
  Finset.univ.sup w

/-- With at least one processor, the max-rule cell value is one of the written values. -/
theorem crcwMax_mem {n : ℕ} (hn : 0 < n) (w : Fin n → ℕ) :
    ∃ i, crcwMax w = w i := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩ w
  exact ⟨i, hi⟩

/-- A processor's value is at most the max-rule cell value. -/
theorem le_crcwMax {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    w i ≤ crcwMax w :=
  Finset.le_sup (s := Finset.univ) (f := w) (Finset.mem_univ i)

/-- OR rule: the cell is `true` iff some processor writes `true`. -/
theorem crcwOr_iff {n : ℕ} (w : Fin n → Bool) :
    crcwOr w = true ↔ ∃ i, w i = true := by
  unfold crcwOr
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

end Cslib.Parallel.PRAM
