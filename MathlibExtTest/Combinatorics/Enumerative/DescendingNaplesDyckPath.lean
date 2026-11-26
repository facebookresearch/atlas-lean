/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.DescendingNaplesDyckPath

open MetaMathlibExt

-- Three cars preferring spot 3 correspond to DDUUUD, which reaches height -2.
example : IsNaplesParkingFunction 2 ![3, 3, 3] ∧ ¬ IsNaplesParkingFunction 1 ![3, 3, 3] := by
  decide

example : IsKDyckPath 3 2 ![false, false, true, true, true, false] ∧
    ¬ IsKDyckPath 3 1 ![false, false, true, true, true, false] := by
  decide

-- UDDU returns to zero and stays above -2, but ends with an Up step.
example : ¬ IsKDyckPath 2 2 ![true, false, false, true] := by decide

example : (Finset.univ.filter (IsKDyckPath 3 1)).card = 9 := by
  rw [← descendingNaplesCount_eq_card_kDyckPath (by decide) (by decide)]
  decide

-- The only preference of length one is already 0-Naples.
example : descendingNaplesCount 1 1 = 1 ∧ descendingStrictNaplesCount 1 1 = 0 := by
  decide

-- Count directly from the parking rule, not from the path formula.
example : descendingNaplesCount 3 1 = 9 ∧ descendingStrictNaplesCount 3 1 = 4 := by
  decide

example : descendingNaplesCount 3 1 = 9 ∧ (descendingStrictNaplesCount 3 1 : ℚ) = 4 := by
  obtain ⟨h, hs⟩ := descendingNaplesCount_eq_choose (n := 3) (k := 1) (by decide) (by decide)
  constructor
  · rw [h]
    decide
  · rw [hs, show Nat.choose (2 * 3) (3 + 1 + 1) = 6 by decide]
    norm_num

-- At k = n, all descending preferences already park with k - 1.
example : descendingNaplesCount 3 3 = 10 ∧ descendingStrictNaplesCount 3 3 = 0 := by
  decide
