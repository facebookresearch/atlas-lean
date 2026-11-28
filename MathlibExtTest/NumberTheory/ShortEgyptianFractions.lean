/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ShortEgyptianFractions

open scoped BigOperators

namespace ShortEgyptianFractionsTest

private def triple : Fin 3 → ℕ := ![2, 3, 6]

private theorem triple_sum : (∑ i : Fin 3, (1 : ℚ) / triple i) = 1 := by
  norm_num [Fin.sum_univ_succ, triple]

-- Compute the bound at every index without the general theorem.
example : ∀ i : Fin 3, triple i ≤ 3 ^ (2 ^ i.val) := by decide

-- The length-one expansion attains the bound at index zero.
example : (∑ i : Fin 1, (1 : ℚ) / (fun _ : Fin 1 ↦ (1 : ℕ)) i) = 1 ∧
    (1 : ℕ) = 1 ^ (2 ^ (0 : Fin 1).val) := by norm_num

-- The empty tuple cannot be an expansion of one.
example : (∑ i : Fin 0, (1 : ℚ) / (Fin.elim0 i : ℕ)) ≠ 1 := by norm_num

example (i : Fin 3) : triple i ≤ 3 ^ (2 ^ i.val) :=
  EgyptianFraction.denominator_le_pow_in_expansion_one
    (by decide) (by decide) triple_sum i

end ShortEgyptianFractionsTest
