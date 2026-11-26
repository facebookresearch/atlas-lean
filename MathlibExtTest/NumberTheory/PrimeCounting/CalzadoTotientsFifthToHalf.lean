/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PrimeCounting.CalzadoTotientsFifthToHalf

/-!
# Tests for the reciprocal-totient limit between two powers
-/

open Filter Topology

example : Tendsto (fun n : ℕ ↦
    ∑ p ∈ (Finset.range (n + 1)).filter (fun p : ℕ ↦ p.Prime ∧
        (n : ℝ) ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt n),
      1 / (Nat.totient p : ℝ)) atTop (𝓝 (Real.log (5 / 2))) := by
  refine (MetaMathlibExt.calzado_sum_inv_totient_fifth_to_half_tendsto.comp
    tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.floor_natCast, Real.sqrt_eq_rpow]

-- The prime at the lower endpoint of the interval for `x = 32` is excluded.
example : 2 ∉ (Finset.range (⌊(32 : ℝ)⌋₊ + 1)).filter (fun p : ℕ ↦ p.Prime ∧
    (32 : ℝ) ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ (32 : ℝ) ^ ((1 : ℝ) / 2)) := by
  have h : (32 : ℝ) ^ ((1 : ℝ) / 5) = 2 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  intro hp
  have hlt := (Finset.mem_filter.mp hp).2.2.1
  rw [h] at hlt
  exact (lt_irrefl (2 : ℝ)) hlt

-- The prime at the upper endpoint of the interval for `x = 4` is included.
example : 2 ∈ (Finset.range (⌊(4 : ℝ)⌋₊ + 1)).filter (fun p : ℕ ↦ p.Prime ∧
    (4 : ℝ) ^ ((1 : ℝ) / 5) < (p : ℝ) ∧ (p : ℝ) ≤ (4 : ℝ) ^ ((1 : ℝ) / 2)) := by
  have h : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hlt : (4 : ℝ) ^ ((1 : ℝ) / 5) < 2 := by
    rw [← h]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hrange : (2 : ℕ) < ⌊(4 : ℝ)⌋₊ + 1 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Nat.floor_natCast]
    decide
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hrange, Nat.prime_two, hlt, h.ge⟩
