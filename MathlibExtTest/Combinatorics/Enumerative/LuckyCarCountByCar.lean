/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.LuckyCarCountByCar

/-! # Tests for counting parking functions in which a given car is lucky -/

open MetaMathlibExt MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- A single car is always lucky, even though the formula has exponent `-1`.
example : (∑ j : Fin 1, (q 1 0 j : ℚ)) = 1 := by
  rw [sum_q_eq 1 0]
  norm_num

-- The first car is lucky in all sixteen parking functions on three spots.
example : (∑ j : Fin 3, (q 3 0 j : ℚ)) = 16 := by
  rw [sum_q_eq 3 0]
  norm_num

-- The last car is lucky in only eight of those parking functions.
example : (∑ j : Fin 3, (q 3 2 j : ℚ)) = 8 := by
  rw [sum_q_eq 3 2]
  norm_num

-- Independently enumerate the preferences for which the last car is lucky.
example : (Finset.univ.filter (fun f : Fin 3 → Fin 3 =>
    IsParkingFunction 3 f ∧ parkSpots f 2 = f 2)).card = 8 := by decide
