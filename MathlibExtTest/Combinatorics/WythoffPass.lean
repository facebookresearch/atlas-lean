/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WythoffPass
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.IntervalCases

namespace MetaMathlibExt.WythoffPassTest

open MetaMathlibExt

-- At the origin the pass is unavailable, while the extra stone can still be taken.
example : wythoffExtraMoveGrundy true 0 0 true = 0 ∧ wythoffExtraMoveGrundy false 0 0 true = 1 :=
  ⟨wythoffPassGrundy_zero_zero true, wythoffPlusStoneGrundy_zero_zero_true⟩

/-! ### The sets `B` and `C` -/

-- `B` and `C` share exactly the positions `(4, 8)` and `(8, 4)`, so together they have
-- `9 + 9 - 2 = 16` positions.
example : wythoffPassSetB ∩ wythoffPassSetC = {(4, 8), (8, 4)} := by decide

example : (wythoffPassSetB ∪ wythoffPassSetC).card = 16 := by decide

-- Both sets are symmetric under swapping the two coordinates.
example : ∀ p ∈ wythoffPassSetB, p.swap ∈ wythoffPassSetB := by decide

example : ∀ p ∈ wythoffPassSetC, p.swap ∈ wythoffPassSetC := by decide

/-! ### Moves into `B` and into `C` -/

-- The hypothesis `9 ≤ x ∨ 9 ≤ y` cannot be dropped: from `(1, 1)` the horizontal move to
-- `(0, 1)` lies in `C`, but no horizontal move lies in `B`.
example : ¬((∃ u < 1, (u, 1) ∈ wythoffPassSetB) ↔ ∃ u < 1, (u, 1) ∈ wythoffPassSetC) := by
  decide

-- From `(n, 8)` with `n ≥ 9`, the horizontal move to `(4, 8) ∈ B` gives a horizontal move into
-- `C`.
example (n : ℕ) (hn : 9 ≤ n) : ∃ u < n, (u, 8) ∈ wythoffPassSetC :=
  (wythoffPass_moves_meet_setB_iff_setC n 8 (Or.inl hn)).1.mp ⟨4, by omega, by decide⟩

-- From `(3, n)` with `n ≥ 9`, the vertical move to `(3, 1) ∈ B` gives a vertical move into `C`
-- (to `(3, 6)`).
example (n : ℕ) (hn : 9 ≤ n) : ∃ v < n, (3, v) ∈ wythoffPassSetC :=
  (wythoffPass_moves_meet_setB_iff_setC 3 n (Or.inr hn)).2.1.mp ⟨1, by omega, by decide⟩

-- From `(n + 12, n + 9)`, the diagonal move with `t = n + 7` reaches `(5, 2) ∈ B`, so some
-- diagonal move reaches `C` (with `t = n + 6`, at `(6, 3)`).
example (n : ℕ) :
    ∃ t, 1 ≤ t ∧ t ≤ n + 12 ∧ t ≤ n + 9 ∧ (n + 12 - t, n + 9 - t) ∈ wythoffPassSetC := by
  refine (wythoffPass_moves_meet_setB_iff_setC (n + 12) (n + 9) (Or.inl (by omega))).2.2.mp
    ⟨n + 7, by omega, by omega, by omega, ?_⟩
  rw [show n + 12 - (n + 7) = 5 by omega, show n + 9 - (n + 7) = 2 by omega]
  decide

-- From `(20, 3)` no diagonal move lies in `B`, whose coordinates differ by at most `4`, so none
-- lies in `C` either.
example : ¬∃ t, 1 ≤ t ∧ t ≤ 20 ∧ t ≤ 3 ∧ (20 - t, 3 - t) ∈ wythoffPassSetC := by
  rw [← (wythoffPass_moves_meet_setB_iff_setC 20 3 (Or.inl (by omega))).2.2]
  rintro ⟨t, -, -, ht, h⟩
  interval_cases t <;> revert h <;> decide

-- At gap four, a diagonal move from (9, 5) reaches (8, 4) in both sets.
example :
    (∃ t, 1 ≤ t ∧ t ≤ 9 ∧ t ≤ 5 ∧ (9 - t, 5 - t) ∈ wythoffPassSetB) ∧
    (∃ t, 1 ≤ t ∧ t ≤ 9 ∧ t ≤ 5 ∧ (9 - t, 5 - t) ∈ wythoffPassSetC) :=
  (wythoffPass_moves_meet_setB_setC 9 5 (Or.inl (by decide))).2.2.1 (by decide) (by decide)

-- At gap five, every legal diagonal move from (4, 9) misses both sets.
example (t : ℕ) (ht : 1 ≤ t) (ht₄ : t ≤ 4) :
    (4 - t, 9 - t) ∉ wythoffPassSetB ∧ (4 - t, 9 - t) ∉ wythoffPassSetC := by
  obtain ⟨missB, missC⟩ :=
    (wythoffPass_moves_meet_setB_setC 4 9 (Or.inr (by decide))).2.2.2 (Or.inr (by decide))
  exact ⟨missB t ht ht₄ (by omega), missC t ht ht₄ (by omega)⟩

end MetaMathlibExt.WythoffPassTest
