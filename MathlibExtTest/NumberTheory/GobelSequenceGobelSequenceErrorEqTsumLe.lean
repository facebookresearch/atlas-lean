/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GobelSequenceGobelSequenceErrorEqTsumLe
import Mathlib.Tactic.NormNum

/-!
# Tests for the Göbel error formula

These tests specialize the error bound to the original Göbel sequence at indices one and two,
and the error formula to the `(3, 2)`-Göbel sequence at index one.
-/

namespace MathlibExtTest.NumberTheory.GobelSequenceGobelSequenceErrorEqTsumLe

open Filter Topology
open MetaMathlibExt

example (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence 2 2 n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n))
      atTop (𝓝 C)) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + 1) / (2 : ℝ) ^ (m + 1)) -
        2 * (Real.log ((2 : ℝ) ^ (1 / 2 : ℝ)) - Real.log C) ≤ 2 / C ^ 2 := by
  obtain ⟨heq, hle⟩ := gobelSequence_error_eq_tsum_le 2 2 (by norm_num) (by norm_num)
    C hC 1 (by norm_num)
  rw [← heq] at hle
  simpa [gobelSequence_one] using hle

example (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence 2 2 n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n))
      atTop (𝓝 C)) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + 2) / (2 : ℝ) ^ (m + 1)) -
        4 * (Real.log ((3 : ℝ) ^ (1 / 4 : ℝ)) - Real.log C) ≤ 4 / C ^ 4 := by
  obtain ⟨heq, hle⟩ := gobelSequence_error_eq_tsum_le 2 2 (by norm_num) (by norm_num)
    C hC 2 (by norm_num)
  rw [← heq] at hle
  have htwo : gobelSequence 2 2 2 = 3 := gobelSequence_two_two_small.1
  norm_num [htwo] at hle
  linarith

-- At `k = 3`, `l = 2` and `n = 1` the equality has weights `3^(m+1)` and exponent `k - 1 = 2`.
example (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence 3 2 n : ℝ) ^ ((1 : ℝ) / (3 : ℝ) ^ n))
      atTop (𝓝 C)) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + 1) / (3 : ℝ) ^ (m + 1)) -
        3 * (Real.log ((2 : ℝ) ^ (1 / 3 : ℝ)) - Real.log C) =
      ∑' m : ℕ, Real.log (1 + ((m + 1 : ℕ) : ℝ) / (gobelSequence 3 2 (m + 1) : ℝ) ^ 2) /
        (3 : ℝ) ^ (m + 1) := by
  have h := (gobelSequence_error_eq_tsum_le 3 2 (by norm_num) (by norm_num) C hC 1 le_rfl).1
  simpa [gobelSequence_one] using h

end MathlibExtTest.NumberTheory.GobelSequenceGobelSequenceErrorEqTsumLe
