/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RascalBinomialSum

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

-- The empty word and the all-zero and all-one words each contribute once.
example : (rascalGen 2 0 0 : ℤ) = 1 := by
  rw [rascalGen_eq_sum 2 0 0 le_rfl]
  decide

example : (rascalGen 2 0 4 : ℤ) = 1 := by
  rw [rascalGen_eq_sum 2 4 0 (by decide)]
  decide

example : (rascalGen 2 4 4 : ℤ) = 1 := by
  rw [rascalGen_eq_sum 2 4 4 le_rfl]
  decide

-- With no ascents the only word is the descending one.
example (n k : ℕ) (hkn : k ≤ n) : (rascalGen 0 k n : ℤ) = 1 := by
  simp [rascalGen_eq_sum 0 n k hkn]

-- With two ones and three zeros, the exact-rise counts are 1, 6, and 3.
example : (rascalGen 1 2 5 : ℤ) = 7 := by
  rw [rascalGen_eq_sum 1 5 2 (by decide)]
  decide

example : (rascalGen 2 2 5 : ℤ) - (rascalGen 1 2 5 : ℤ) = 3 := by
  rw [rascalGen_eq_sum 2 5 2 (by decide), rascalGen_eq_sum 1 5 2 (by decide)]
  decide

-- An ascent bound above the maximum adds no words.
example : (rascalGen 4 2 5 : ℤ) = (rascalGen 2 2 5 : ℤ) := by
  rw [rascalGen_eq_sum 4 5 2 (by decide), rascalGen_eq_sum 2 5 2 (by decide)]
  decide

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
