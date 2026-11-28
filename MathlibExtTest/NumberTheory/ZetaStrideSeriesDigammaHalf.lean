/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ZetaStrideSeriesDigammaHalf

/-! # Tests for the half-shift digamma series -/

open Filter Finset MetaMathlibExt Topology

private noncomputable def halfShiftTerm (q n : ℕ) : ℝ :=
  (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1 + 1 / 2) * ((n : ℝ) + 1 - 1 / 2 + q)) *
    strideAlternatingSum q 1 (n + 1)

private noncomputable def halfShiftLimit (q : ℕ) : ℂ :=
  (∑' n : ℕ, 1 / ((n : ℂ) + 1) *
    (Complex.digamma (((n : ℂ) + 1 + 1 / 2 + q) / (2 * q)) -
      Complex.digamma (((n : ℂ) + 1 + 1 / 2) / (2 * q)))) / (2 * q) +
  (∑' n : ℕ, 1 / ((n : ℂ) + 1) *
    (Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2 * q) / (2 * q)) -
      Complex.digamma (((n : ℂ) + 1 - 1 / 2 + q) / (2 * q)))) / (2 * q)

private theorem tendsto_tail_of_prefix (q k : ℕ) (hq : 0 < q) {c : ℝ}
    (hc : ∑ n ∈ range k, halfShiftTerm q n = c) :
    Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ range N, halfShiftTerm q (k + n)) : ℂ))
      atTop (𝓝 (halfShiftLimit q - c)) := by
  have h : Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ range N, halfShiftTerm q n) : ℂ))
      atTop (𝓝 (halfShiftLimit q)) := by
    simpa only [halfShiftTerm, halfShiftLimit, pow_one] using
      tendsto_strideAlternatingSum_digamma_half q 1 hq (by decide)
  have hshift : Tendsto (fun N : ℕ ↦ k + N) atTop atTop := by
    simpa only [Nat.add_comm k] using tendsto_add_atTop_nat k
  have hconst : Tendsto (fun _ : ℕ ↦ (c : ℂ)) atTop (𝓝 (c : ℂ)) := tendsto_const_nhds
  simpa only [Function.comp_apply, sum_range_add, hc, Complex.ofReal_add, add_sub_cancel_left]
    using (h.comp hshift).sub hconst

-- The first two terms at stride one sum to 14/15, including the first negative term.
example :
    Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ range N, halfShiftTerm 1 (2 + n)) : ℂ))
      atTop (𝓝 (halfShiftLimit 1 - ↑(14 / 15 : ℝ))) := by
  apply tendsto_tail_of_prefix 1 2 (by decide)
  norm_num [halfShiftTerm, strideAlternatingSum.eq_def, sum_range_succ]

-- At stride two the first four terms cross the first subtraction in both residue classes.
example :
    Tendsto (fun N : ℕ ↦ (↑(∑ n ∈ range N, halfShiftTerm 2 (4 + n)) : ℂ))
      atTop (𝓝 (halfShiftLimit 2 - ↑(10082 / 10395 : ℝ))) := by
  apply tendsto_tail_of_prefix 2 4 (by decide)
  norm_num [halfShiftTerm, strideAlternatingSum.eq_def, sum_range_succ]

-- The shared finite bound applies to the nonconstant sequence 1, 2, 3.
example :
    ‖∑ i ∈ range 3, (-1 : ℝ) ^ i * ((i : ℝ) + 1)‖ = 2 ∧
      ‖∑ i ∈ range 3, (-1 : ℝ) ^ i * ((i : ℝ) + 1)‖ ≤ 6 := by
  constructor
  · norm_num [sum_range_succ, Real.norm_eq_abs]
  · have h := norm_sum_range_neg_one_pow_mul_le_two_mul (fun i ↦ (i : ℝ) + 1) 2
      (fun i _ ↦ by positivity) (fun i _ ↦ by simp [Nat.cast_add])
    convert h using 1
    norm_num
