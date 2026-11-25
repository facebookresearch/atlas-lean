/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SmallHouse

/-! # Endpoint tests for the classification of small houses -/

open NumberField MathlibExt.NumberTheory.SmallHouseWanted.NumberTheory
open scoped Real

namespace MathlibExt.NumberTheory.SmallHouseWanted.NumberTheory.SmallHouseTest

private local instance rationalCyclotomic : IsCyclotomicExtension {1} ℚ ℚ :=
  IsCyclotomicExtension.singleton_one_of_algebraMap_bijective Function.surjective_id

-- The zero integer forces the cosine branch.
example : ∃ m : ℕ, 0 < m ∧ Real.cos (π / m) = 0 := by
  have h0 : house (0 : ℚ) = 0 := by simpa using house_intCast (K := ℚ) 0
  have h := cyclotomic_integer_house_le_two 1 (isIntegral_zero (R := ℤ) (B := ℚ))
    (maximalRealSubfield ℚ).zero_mem (by rw [h0]; norm_num)
  rw [h0] at h
  obtain ⟨m, hm, he⟩ := h.resolve_left (by norm_num)
  exact ⟨m, hm, by linarith⟩

-- A negative integer attains the upper endpoint, which no finite positive index gives.
example : house (-2 : ℚ) = 2 := by
  have hbound : house (((-2 : ℤ) : ℚ)) ≤ 2 := by rw [house_intCast]; norm_num
  apply (cyclotomic_integer_house_le_two 1 (isIntegral_intCast (R := ℤ) (-2))
    ((maximalRealSubfield ℚ).intCast_mem (-2)) hbound).resolve_right
  rintro ⟨m, hm, he⟩
  have hangle : π / m ≤ π := div_le_self Real.pi_pos.le (by exact_mod_cast hm)
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) le_rfl hangle (by positivity)
  rw [Real.cos_zero] at hcos
  rw [house_intCast] at he
  norm_num at he
  linarith

end MathlibExt.NumberTheory.SmallHouseWanted.NumberTheory.SmallHouseTest
