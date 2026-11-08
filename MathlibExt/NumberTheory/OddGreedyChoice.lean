/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Bounds.Basic

/-!
# Odd greedy choice

The one-step choice in the odd greedy (Egyptian) expansion of a positive
rational: the least positive odd denominator whose unit fraction does not
exceed the remainder. Shared by the odd greedy expansion termination
conjecture (`OpenConjectures.NumberTheory.OddGreedyExpansionTermination`)
and the Louwsma--Martino first-denominator characterization
(`WantedExt.NumberTheory.OddGreedyExpansionWanted`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- At a positive remainder `r`, `d` is the odd greedy choice: the smallest
positive odd denominator whose unit fraction does not exceed `r`
(equivalently, the largest admissible odd unit fraction `1 / d`). -/
def IsOddGreedyChoice (r : ℚ) (d : ℕ) : Prop :=
  0 < r ∧ 0 < d ∧ Odd d ∧ (1 : ℚ) / (d : ℚ) ≤ r ∧
    ∀ e : ℕ, 0 < e → Odd e → (1 : ℚ) / (e : ℚ) ≤ r → d ≤ e

/-- The odd greedy choice is taken at a positive remainder. -/
theorem IsOddGreedyChoice.pos_r {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : 0 < r :=
  h.1

/-- The odd greedy choice is a positive denominator. -/
theorem IsOddGreedyChoice.pos_d {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : 0 < d :=
  h.2.1

/-- The odd greedy choice is odd. -/
theorem IsOddGreedyChoice.odd {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : Odd d :=
  h.2.2.1

/-- The unit fraction of the odd greedy choice does not
exceed the remainder. -/
theorem IsOddGreedyChoice.inv_le {r : ℚ} {d : ℕ}
    (h : IsOddGreedyChoice r d) : (1 : ℚ) / (d : ℚ) ≤ r :=
  h.2.2.2.1

/-- The odd greedy choice is the least admissible
positive odd denominator. -/
theorem IsOddGreedyChoice.min {r : ℚ} {d e : ℕ}
    (h : IsOddGreedyChoice r d) (he : 0 < e) (hodd : Odd e)
    (hle : (1 : ℚ) / (e : ℚ) ≤ r) : d ≤ e :=
  h.2.2.2.2 e he hodd hle

/-- The odd greedy choice at a given remainder is unique. -/
theorem IsOddGreedyChoice.unique {r : ℚ} {d d' : ℕ}
    (h : IsOddGreedyChoice r d) (h' : IsOddGreedyChoice r d') :
    d = d' :=
  le_antisymm (h.min h'.pos_d h'.odd h'.inv_le)
    (h'.min h.pos_d h.odd h.inv_le)

/-- `d` is the odd greedy choice at `r` iff `r` is positive and `d` is
the least positive odd denominator whose unit fraction does not
exceed `r`. -/
theorem isOddGreedyChoice_iff {r : ℚ} {d : ℕ} :
    IsOddGreedyChoice r d ↔
      0 < r ∧ IsLeast {e : ℕ | 0 < e ∧ Odd e ∧ (1 : ℚ) / (e : ℚ) ≤ r} d := by
  constructor
  · intro h
    exact ⟨h.pos_r, ⟨⟨h.pos_d, h.odd, h.inv_le⟩,
      fun e he => h.min he.1 he.2.1 he.2.2⟩⟩
  · rintro ⟨hr, ⟨hd, hodd, hle⟩, hmin⟩
    exact ⟨hr, hd, hodd, hle, fun e he hodd' hle' =>
      hmin ⟨he, hodd', hle'⟩⟩

end

end MetaMathlibExt
