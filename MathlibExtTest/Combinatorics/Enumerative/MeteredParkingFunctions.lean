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
