/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SquareWeightedZeroSumTwoPower
import Mathlib.Tactic.FinCases

/-! # Tests for the square-weighted zero-sum obstruction modulo even powers of two -/

open MetaMathlibExt

-- The smallest positive even exponent, where reduction modulo four is the identity.
example : ¬ HasWeightedZeroSumSubseq (squareSet 4) (fun _ : Fin 3 => 1) := by
  exact no_squareWeightedSubseq_three_units_twoPower 2 (by decide) (by decide) _
    (fun _ => isUnit_one) (fun _ => by decide)

-- Distinct lifts of one modulo four, where nonunit square weights are also possible.
example : ¬ HasWeightedZeroSumSubseq (squareSet 16) (![1, 5, 13] : Fin 3 → ZMod 16) := by
  apply no_squareWeightedSubseq_three_units_twoPower 4 (by decide) (by decide)
  · intro i
    fin_cases i
    · exact (ZMod.isUnit_iff_coprime 1 16).mpr (by decide)
    · exact (ZMod.isUnit_iff_coprime 5 16).mpr (by decide)
    · exact (ZMod.isUnit_iff_coprime 13 16).mpr (by decide)
  · intro i
    fin_cases i <;> decide
