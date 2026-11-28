/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.AlmostPrimeUniformUpperBound
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- At the endpoint `t = 1`, the bound forces the count to vanish for every `k ≥ 1`.
example (k : ℕ) (hk : 1 ≤ k) : almostPrimeCounting (k + 1) 1 = 0 := by
  obtain ⟨C, hC⟩ := almostPrime_count_le_erdos_sarkozy
  have h : (almostPrimeCounting (k + 1) 1 : ℝ) ≤ 0 := by
    simpa using hC k hk 1 le_rfl
  exact Nat.le_zero.mp (by exact_mod_cast h)

-- One constant works simultaneously for semiprimes and integers with three prime factors,
-- including at nonintegral counting cutoffs.
example : ∃ C : ℝ,
    (almostPrimeCounting 2 ⌊(9 / 2 : ℝ)⌋₊ : ℝ) ≤ C * (1 / 2) * (9 / 2) * Real.log (9 / 2) ∧
    (almostPrimeCounting 3 ⌊(17 / 2 : ℝ)⌋₊ : ℝ) ≤ C * 4 * (17 / 2) * Real.log (17 / 2) := by
  obtain ⟨C, hC⟩ := almostPrime_count_le_erdos_sarkozy
  refine ⟨C, ?_, ?_⟩
  · simpa using hC 1 le_rfl (9 / 2) (by norm_num)
  · have h4 : (2 : ℝ) ^ 4 / 2 ^ (2 : ℕ) = 4 := by norm_num
    simpa only [Nat.cast_ofNat, h4] using hC 2 (by decide) (17 / 2) (by norm_num)

end MetaMathlibExt
