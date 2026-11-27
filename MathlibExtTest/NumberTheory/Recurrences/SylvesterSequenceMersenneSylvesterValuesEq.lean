/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import MathlibExt.NumberTheory.Recurrences.SylvesterSequenceMersenneSylvesterValuesEq

open MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

namespace MathlibExtTest.NumberTheory.Recurrences.SylvesterSequenceMersenneSylvesterValuesEq

-- 3 is a Mersenne Sylvester number.
example : 3 ∈ {x : ℕ | ∃ n r : ℕ, 1 ≤ r ∧ x = sylvesterNumber n ∧
    x = 2 ^ r - 1} := by
  rw [mersenne_sylvester_values_eq]
  decide

-- 7 is a Mersenne Sylvester number.
example : 7 ∈ {x : ℕ | ∃ n r : ℕ, 1 ≤ r ∧ x = sylvesterNumber n ∧
    x = 2 ^ r - 1} := by
  rw [mersenne_sylvester_values_eq]
  decide

-- S₃ = 43 is not a Mersenne Sylvester number.
example : sylvesterNumber 3 ∉ {x : ℕ | ∃ n r : ℕ, 1 ≤ r ∧
    x = sylvesterNumber n ∧ x = 2 ^ r - 1} := by
  rw [mersenne_sylvester_values_eq]
  decide

end MathlibExtTest.NumberTheory.Recurrences.SylvesterSequenceMersenneSylvesterValuesEq
