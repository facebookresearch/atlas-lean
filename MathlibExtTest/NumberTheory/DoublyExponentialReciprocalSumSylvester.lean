/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumSylvester
import Mathlib.Tactic.NormNum

/-!
# Tests for the Sylvester sequence characterization

The characterization determines the initial denominators, including a case of equality in
its upper ratio bound, and gives the Sylvester recurrence at every index.
-/

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumSylvester

variable {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
  (hratio : ∀ n, 2 / 3 ≤ (a n : ℝ) ^ 2 / a (n + 1) ∧ (a n : ℝ) ^ 2 / a (n + 1) ≤ 4 / 3)
  (hsum : HasSum (fun n => 1 / (a n : ℝ)) 1)

-- The unit-fraction remainders force the four initial denominators.
example : a 0 = 2 ∧ a 1 = 3 ∧ a 2 = 7 ∧ a 3 = 43 := by
  have heq := eq_sylvester_of_ratio_mem_of_hasSum_one hpos hratio hsum
  rw [heq 0, heq 1, heq 2, heq 3]
  decide

-- The upper endpoint of Koizumi's ratio interval is attained at the initial index.
example : (a 0 : ℝ) ^ 2 / a 1 = 4 / 3 := by
  have heq := eq_sylvester_of_ratio_mem_of_hasSum_one hpos hratio hsum
  rw [heq 0, heq 1]
  norm_num [Nat.generalizedSylvester]

example (n : ℕ) : a (n + 1) = a n ^ 2 - a n + 1 := by
  simp only [eq_sylvester_of_ratio_mem_of_hasSum_one hpos hratio hsum,
    Nat.generalizedSylvester_succ]

end MathlibExtTest.NumberTheory.DoublyExponentialReciprocalSumSylvester
