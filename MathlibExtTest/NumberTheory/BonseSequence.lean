/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BonseSequence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Prime.Nth

open Filter Topology MathlibExt.NumberTheory.BonseWanted

-- Zero has the stipulated default, while positive indices start with the first prime.
example : primeNth 0 = 2 ∧ primeNth 1 = 2 ∧ primeNth 2 = 3 := by
  simp [primeNth]

-- This sequence has log-product ratio 1 - 2⁻ⁿ and satisfies the regularity limit.
example : ¬ IsBonseSeq (fun n : ℕ => 2 ^ 2 ^ n) := by
  have htwo : 1 < (2 : ℕ) := by decide
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm (n : ℕ) : Real.log ((2 ^ 2 ^ n : ℕ) : ℝ) = 2 ^ n * Real.log 2 := by
    simp [Nat.cast_pow, Real.log_pow]
  apply not_isBonseSeq_of_liminf_lt
  · exact (pow_right_strictMono₀ htwo).comp (pow_right_strictMono₀ htwo)
  · intro n
    exact Nat.succ_le_of_lt (by positivity)
  · simp only [hterm, Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hlog.ne',
      Real.log_pow]
    have hpoly (k : ℕ) := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
    have h := (((hpoly 2).add (hpoly 1)).const_mul (Real.log 2)).add
      (((hpoly 1).add (hpoly 0)).const_mul (Real.log (Real.log 2)))
    convert h.div_const (2 * Real.log 2) using 1
    · ext n
      simp only [pow_succ (2 : ℝ) n, pow_one, pow_zero]
      ring
    · simp
  · refine ⟨1, by norm_num, Eventually.frequently (.of_forall fun n => ?_)⟩
    rw [Real.log_prod (fun k _ => by positivity)]
    simp only [hterm, ← Finset.sum_mul]
    rw [div_lt_one (by positivity), mul_lt_mul_iff_left₀ hlog]
    have h := geom_sum_mul (2 : ℝ) n
    linarith
