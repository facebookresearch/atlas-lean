/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import MathlibExt.NumberTheory.UnitWeightedZeroSumPrimePower

open MetaMathlibExt

-- The two equal unit terms occupy different positions, separated by a nonzero nonunit.
example : ∃ a : Fin 3 → ZMod 9, (∀ i, IsUnit (a i)) ∧ a 0 + a 1 * 3 + a 2 = 0 := by
  obtain ⟨a, ha, hsum⟩ := unit_weighted_zero_sum_prime_power 3 2 3 (by decide) (by decide)
    ![1, 3, 1] (by decide)
  exact ⟨a, ha, by simpa [Fin.sum_univ_three] using hsum⟩

-- At the smallest odd prime the sum of three unit terms can also be cancelled.
example : ∃ a : Fin 3 → ZMod 3, (∀ i, IsUnit (a i)) ∧ a 0 + a 1 + a 2 * 2 = 0 := by
  obtain ⟨a, ha, hsum⟩ := unit_weighted_zero_sum_prime_power 3 1 3 (by decide) (by decide)
    ![1, 1, 2] (by decide)
  exact ⟨a, ha, by simpa [Fin.sum_univ_three] using hsum⟩
