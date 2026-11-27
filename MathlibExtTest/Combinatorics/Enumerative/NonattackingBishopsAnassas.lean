/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NonattackingBishopsAnassas

open MetaMathlibExt

-- The empty placement and the single white square are both counted.
example : bishopsSquare 0 0 = 1 := by decide
example : bishopsWhite 1 1 = 1 ∧ bishopsBlack 1 1 = 0 := by decide

-- Direct enumeration: the four legal pairs occupy a common row or a common column.
example : bishopsSquare 2 2 = 4 := by decide

-- The odd board has placements with four bishops; a fifth bishop is impossible.
example : bishopsSquare 3 4 = 8 := by
  rw [bishopsSquare_eq_sum]
  decide

example : bishopsSquare 3 5 = 0 := by
  rw [bishopsSquare_eq_sum]
  decide

-- The extension uses unsigned first-kind numbers for negative arguments.
example : extStirlingSecond (-1) (-3) = 2 ∧ extStirlingSecond 0 (-1) = 0 := by decide

-- Ward's identity on the diagonal, at the other endpoint, and with contributions from
-- both a triple and two pairs: `S(5, 3) = 10 + 15`.
example : (Nat.stirlingSecond 5 (5 - 0) : ℤ) = 1 :=
  (stirlingSecond_sub_eq_sum_associated (m := 5) (k := 0) (hk := by decide)).trans (by decide)

example : (Nat.stirlingSecond 5 (5 - 5) : ℤ) = 0 :=
  (stirlingSecond_sub_eq_sum_associated (m := 5) (k := 5) (hk := by decide)).trans (by decide)

example : (Nat.stirlingSecond 5 (5 - 2) : ℤ) = 10 + 15 :=
  (stirlingSecond_sub_eq_sum_associated (m := 5) (k := 2) (hk := by decide)).trans (by decide)

-- The boundary clauses include the empty board, no pieces, and both sides of the diagonal.
example : anassasBelow 0 0 0 = 1 := by
  simpa using (anassasBelow_recurrence (m := 0) (k := 0) (p := 0)).2.1

example : anassasBelow 0 1 0 = 0 := by
  simpa using (anassasBelow_recurrence (m := 2) (k := 1) (p := 0)).2.1

example : anassasBelow 2 0 1 = 0 := by
  simpa using (anassasBelow_recurrence (m := 2) (k := 0) (p := 1)).2.2.1

example : anassasBelow 3 1 0 = 6 ∧ anassasBelow 3 1 1 = 3 ∧ anassasBelow 3 1 2 = 0 := by
  refine ⟨(anassasBelow_recurrence 3 0 0).2.2.2.1.trans (by decide),
    (anassasBelow_recurrence 3 0 1).2.2.2.1.trans (by decide),
    (anassasBelow_recurrence 3 0 2).2.2.2.1.trans (by decide)⟩

example : anassasBelow 3 2 0 = 7 := by
  exact (anassasBelow_recurrence 3 2 0).2.2.2.2.trans (by decide)

-- All four terms of the recurrence contribute here. Also check against enumeration.
example : anassasBelow 3 2 1 = 14 := by decide

example : (anassasBelow 3 2 1 : ℤ) = 14 :=
  (anassasBelow_recurrence 2 0 0).1.trans (by decide)

-- Impossible counts kill the terms with negative integer coefficients.
example : (anassasBelow 2 4 1 : ℤ) = 0 :=
  (anassasBelow_recurrence 1 2 0).1.trans (by decide)

example : (anassasBelow 2 2 3 : ℤ) = 0 :=
  (anassasBelow_recurrence 1 0 2).1.trans (by decide)
