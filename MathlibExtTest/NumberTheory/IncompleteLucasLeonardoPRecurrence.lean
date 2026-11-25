/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.IncompleteLucasLeonardoPRecurrence
import Mathlib.Tactic.NormNum

/-!
# Tests for the incomplete Lucas-Leonardo recurrence
-/

open MetaMathlibExt

-- At the first admissible board length, use the zero cutoff and the shortest positive lag.
example (p : ℕ) (hp : 1 ≤ p) :
    incompleteLucasLeonardoP p (p + 2) 1 = incompleteLucasLeonardoP p (p + 1) 1 + 1 + p := by
  simpa [show p + 2 - p - 1 = 1 by omega, incompleteLucasLeonardoP_zero p 1 (by decide)] using
    incompleteLucasLeonardoP_succ p (p + 2) 0 hp (by omega) (Nat.zero_le _)

-- At a divisible board length and maximum cutoff, the preceding board has lower capacity.
example : incompleteLucasLeonardoP 2 6 3 = 28 := by
  rw [incompleteLucasLeonardoP_succ 2 6 2 (by decide) (by decide) (by decide)]
  norm_num [incompleteLucasLeonardoP, Finset.sum_range_succ, Nat.choose]

-- Above-capacity terms can have zero denominator even at positive board lengths.
example : incompleteLucasLeonardoP 1 3 2 = 7 := by
  rw [incompleteLucasLeonardoP_succ 1 3 1 (by decide) (by decide) (by decide)]
  norm_num [incompleteLucasLeonardoP, Finset.sum_range_succ, Nat.choose]

-- At a nondivisible board length and an interior cutoff, both sums have nonzero higher terms.
example : incompleteLucasLeonardoP 2 10 2 = 106 := by
  rw [incompleteLucasLeonardoP_succ 2 10 1 (by decide) (by decide) (by decide)]
  norm_num [incompleteLucasLeonardoP, Finset.sum_range_succ, Nat.choose]
