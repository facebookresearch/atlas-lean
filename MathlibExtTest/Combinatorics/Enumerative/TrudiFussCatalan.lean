/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrudiFussCatalan
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The totalized parameters give zero in every positive degree.
example (n : ℕ) (hn : 1 ≤ n) :
    -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 0 i 0 : ℚ)) n = 0 := by
  simpa using trudiPartitionSum_fussCatalan.1 0 0 n hn

-- A negative binomial upper index gives a genuinely negative value.
example : -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 0 i 2 : ℚ)) 2 = -3 := by
  rw [trudiPartitionSum_fussCatalan.1 0 2 2 (by decide)]
  norm_num [Ring.choose_one_right]

-- The two shifts start with different Catalan differences.
example : -trudiPartitionSum (-1) (fun i => (catalan i : ℚ) - catalan (i - 1)) 1 = 0 ∧
    -trudiPartitionSum (-1) (fun i => (catalan (i + 1) : ℚ) - catalan i) 1 = 1 := by
  constructor
  · simpa using trudiPartitionSum_fussCatalan.2.1 1 (by decide)
  · simpa using trudiPartitionSum_fussCatalan.2.2.1 1 (by decide)

-- Degree two is the first degree unaffected by the linear correction in the ternary shift.
example : -trudiPartitionSum (-1) (fun i => (generalizedFussCatalanNumber 3 (i + 1) 1 : ℚ)) 2 =
    3 := by
  rw [trudiPartitionSum_fussCatalan.2.2.2.1 2 (by decide)]
  norm_num

-- The first part of a composition of one uses the constant Fuss–Catalan coefficient.
example : trudiPartitionSum 1 (fun i => (generalizedFussCatalanNumber 3 (i - 1) 2 : ℚ)) 1 = 1 := by
  rw [trudiPartitionSum_fussCatalan.2.2.2.2 1 (by decide), generalizedFussCatalanNumber_one]
  norm_num
