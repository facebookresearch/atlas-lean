/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions

open MetaMathlibExt

-- The third car moves exactly two spots, attaining the displacement bound.
example : 3 ≤ (1 : ℕ) + 2 :=
  (meteredOutcome_displacement_le (t := 2) (![1, 1, 1] : Fin 3 → Fin 4) 2).1 3 (by decide)

-- A repeat preference for the last spot fails at the exact threshold.
example : 4 ≤ (3 : ℕ) + 1 :=
  (meteredOutcome_displacement_le (t := 1) (![3, 3] : Fin 2 → Fin 4) 1).2 (by decide)

-- With meter zero previous arrivals do not block even the last spot.
example : meteredOutcome 0 3 [2, 2, 0] = [some 2, some 2, some 0] := by decide

-- A meter longer than the whole list remembers every prior arrival.
example : meteredOutcome 5 3 [0, 0, 0] = [some 0, some 1, some 2] := by decide

example : meteredOutcome 2 0 [] = [] := by decide

-- At the meter threshold the third arrival fails, even though the fourth can park.
example : meteredOutcome 2 2 [0, 0, 0, 0] = [some 0, some 1, none, some 0] := by decide

example : meteredParkingCount 2 3 2 = 0 := by decide

-- Reducing the meter by one or removing one car allows successful preferences.
example : meteredParkingCount 1 3 2 = 4 := by decide

example : meteredParkingCount 2 2 2 = 3 := by decide

-- With no spots the empty preference list is the only successful one.
example : meteredParkingCount 0 1 0 = 0 ∧ meteredParkingCount 0 0 0 = 1 := by decide

private def admissibleFirstEntries {m n : ℕ} (π : Fin m → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => IsPartialParkingFunction (m + 1) n (Fin.cons j π)

-- In Example 8, six first entries succeed and the last two fail.
example :
    admissibleFirstEntries (![2, 6, 1, 0, 6, 1] : Fin 6 → Fin 8) = {0, 1, 2, 3, 4, 5} ∧
      IsParkingShuffle 6 8 6 ![2, 6, 1, 0, 6, 1] ∧
      ¬ IsParkingShuffle 6 8 7 ![2, 6, 1, 0, 6, 1] := by decide

-- At `k = n` every insertion succeeds, even with a nonempty tail.
example :
    admissibleFirstEntries (![0, 1] : Fin 2 → Fin 3) = Finset.univ ∧
      IsParkingShuffle 2 3 3 ![0, 1] := by decide

-- At `k = 1` only the first spot is admissible, and the lower word is empty.
example :
    admissibleFirstEntries (![1, 2] : Fin 2 → Fin 3) = {0} ∧
      IsParkingShuffle 2 3 1 ![1, 2] := by decide

-- For an empty tail, every spot is admissible, and only `k = n` is a shuffle parameter.
example :
    admissibleFirstEntries (![] : Fin 0 → Fin 3) = Finset.univ ∧
      IsParkingShuffle 0 3 3 ![] ∧ ¬ IsParkingShuffle 0 3 2 ![] := by decide

-- A tail can also overflow a threshold before the first entry is added.
example :
    admissibleFirstEntries (![2, 2] : Fin 2 → Fin 3) = ∅ ∧
      ∀ k ∈ Finset.Icc 1 3, ¬ IsParkingShuffle 2 3 k ![2, 2] := by decide

-- Use the public theorem to recover the admissible set from a one-letter shuffle.
example : admissibleFirstEntries (![2] : Fin 1 → Fin 3) = {0, 1} := by
  have h := (firstEntrySet_eq_iff_isParkingShuffle (m' := 1) (n := 3) (k := 2)
    (by decide) (by decide) ![2]).mpr (by decide)
  exact h.trans (by decide)
