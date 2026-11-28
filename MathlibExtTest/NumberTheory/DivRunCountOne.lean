/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivRunCountOne

namespace MetaMathlibExt

-- At bound zero the only candidate has a zero divisor.
example : divRunCount 0 1 = 0 := by decide

-- Count directly from the run predicate at a bound with more than one divisor magnitude.
example : divRunCount 2 1 = 1980 := by decide +kernel

-- The closed formula agrees with that direct count.
example : divRunCount 2 1 = 1980 := by
  rw [divRunCount_one]
  decide

-- One constant controls the error at the smallest permitted bound and all larger bounds.
example : ∃ K : ℝ, |1980 - 32 * 2 ^ 4 * Real.log 2| ≤ K * 2 ^ 4 ∧
    ∀ B : ℕ, 3 ≤ B →
      |(divRunCount B 1 : ℝ) - 32 * (B : ℝ) ^ 4 * Real.log B| ≤ K * (B : ℝ) ^ 4 := by
  obtain ⟨K, hK⟩ := divRunCount_one_asymptotic
  have hcount : divRunCount 2 1 = 1980 := by
    rw [divRunCount_one]
    decide
  exact ⟨K, by simpa [hcount] using hK 2 (by decide), fun B hB => hK B (by omega)⟩

end MetaMathlibExt
