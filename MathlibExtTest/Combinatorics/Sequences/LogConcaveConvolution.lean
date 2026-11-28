/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.LogConcaveConvolution
import MathlibExt.Combinatorics.Sequences.Unimodal

open MathlibExt.Combinatorics.Sequences.Unimodal

namespace MetaMathlibExt

private noncomputable def sampleX (n : ℕ) : ℝ := (n : ℝ) + 1
private noncomputable def sampleY (n : ℕ) : ℝ := 2 ^ n

private noncomputable def sampleConvolution (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), sampleX k * sampleY (n - k)

private lemma sampleConvolution_values :
    sampleConvolution 0 = 1 ∧ sampleConvolution 1 = 4 ∧
      sampleConvolution 2 = 11 ∧ sampleConvolution 3 = 26 := by
  norm_num [sampleConvolution, sampleX, sampleY, Finset.sum_range_succ]

-- Check the first two midpoint inequalities independently by evaluating the sums.
example : sampleConvolution 0 * sampleConvolution 2 < sampleConvolution 1 ^ 2 ∧
    sampleConvolution 1 * sampleConvolution 3 < sampleConvolution 2 ^ 2 := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := sampleConvolution_values
  norm_num [h₀, h₁, h₂, h₃]

-- A client uses the public theorem on the same distinct factors.
example : sampleConvolution 0 * sampleConvolution 2 ≤ sampleConvolution 1 ^ 2 := by
  refine logConcave_convolution sampleX sampleY (fun n => by unfold sampleX; positivity)
    (fun n => by unfold sampleY; positivity) ?_ ?_ 1 (by decide)
  · intro i hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    simp only [sampleX, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    nlinarith
  · intro i hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    simp only [sampleY, Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ (2 : ℝ)]
    ring_nf
    exact le_rfl

private noncomputable def samplePrefix (i : ℕ) : ℝ :=
  if i ≤ 2 then sampleX i else if i = 3 then 10 else 0

-- The centered inequality holds at 1 but fails at 2, so index 2 must be excluded
-- when the last index is 2. Check both inequalities without the midpoint criterion.
example : samplePrefix 0 * samplePrefix 2 < samplePrefix 1 ^ 2 ∧
    samplePrefix 2 ^ 2 < samplePrefix 1 * samplePrefix 3 := by
  norm_num [samplePrefix, sampleX]

example : IsLogConcave samplePrefix 2 := by
  apply isLogConcave_iff_mul_le_sq.mpr
  intro i hi hi'
  have : i = 1 := by omega
  subst i
  norm_num [samplePrefix, sampleX]

example : ¬ IsLogConcave samplePrefix 3 := by
  intro h
  have h₂ := isLogConcave_iff_mul_le_sq.mp h 2 (by decide) (by decide)
  norm_num [samplePrefix, sampleX] at h₂

-- Check the positive prefix and the zero outside it without using the no-zero lemma.
private lemma samplePrefix_pos (i : ℕ) (hi : i ≤ 2) : 0 < samplePrefix i := by
  simp only [samplePrefix, ite_eq_left hi, sampleX]
  positivity

example : samplePrefix 4 = 0 := by norm_num [samplePrefix]
example : NoInternalZeros samplePrefix 2 := NoInternalZeros.of_pos samplePrefix_pos

end MetaMathlibExt
