/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.FloorFiberSets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for the Beatty sets of floor-fiber multiplicities -/

namespace MathlibExtTest.NumberTheory.Beatty.FloorFiberSets

open Set

private theorem sqrt_two_bounds : 4 / 3 < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 := by
  exact ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num),
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)⟩

-- For slope `1 / √2`, exactly index 2 gives value 1.
private theorem fiber_one :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (Real.sqrt 2)⁻¹⌋ = (1 : ℤ)} = {2} := by
  obtain ⟨hl, hu⟩ := sqrt_two_bounds
  have hs : 0 < Real.sqrt 2 := by linarith
  ext n
  simp only [mem_ofPred_eq, mem_singleton_iff, Int.floor_eq_iff, ← div_eq_mul_inv, Int.cast_one,
    le_div_iff₀ hs, div_lt_iff₀ hs]
  constructor
  · rintro ⟨_, hlo, hhi⟩
    have h₁ : (1 : ℝ) < n := by linarith
    have h₂ : (n : ℝ) < 3 := by linarith
    have hn₁ : 1 < n := by exact_mod_cast h₁
    have hn₂ : n < 3 := by exact_mod_cast h₂
    omega
  · rintro rfl
    norm_num
    linarith

-- For the same slope, exactly indices 3 and 4 give value 2.
private theorem fiber_two :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (Real.sqrt 2)⁻¹⌋ = (2 : ℤ)} = {3, 4} := by
  obtain ⟨hl, hu⟩ := sqrt_two_bounds
  have hs : 0 < Real.sqrt 2 := by linarith
  ext n
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Int.floor_eq_iff, ← div_eq_mul_inv,
    Int.cast_ofNat, le_div_iff₀ hs, div_lt_iff₀ hs]
  constructor
  · rintro ⟨_, hlo, hhi⟩
    have h₁ : (2 : ℝ) < n := by linarith
    have h₂ : (n : ℝ) < 5 := by linarith
    have hn₁ : 2 < n := by exact_mod_cast h₁
    have hn₂ : n < 5 := by exact_mod_cast h₂
    omega
  · rintro (rfl | rfl) <;> norm_num <;> constructor <;> linarith

-- At the minimum `k = 1`, check both multiplicity classes and the exclusion of zero.
example : ∃ γ δ : ℝ,
    (2 : ℤ) ∈ {beattySeq γ m | m > 0} ∧ (1 : ℤ) ∈ {beattySeq δ m | m > 0} ∧
    (0 : ℤ) ∉ {beattySeq γ m | m > 0} ∧ (0 : ℤ) ∉ {beattySeq δ m | m > 0} := by
  obtain ⟨hl, hu⟩ := sqrt_two_bounds
  have hs : 0 < Real.sqrt 2 := by linarith
  have hlo : 1 / ((1 : ℝ) + 1) < (Real.sqrt 2)⁻¹ := by
    rw [one_div, inv_lt_inv₀ (by positivity) hs]
    linarith
  have hhi : (Real.sqrt 2)⁻¹ < 1 / (1 : ℝ) := by
    rw [div_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨γ, δ, _, _, hγ, hδ⟩ :=
    MetaMathlibExt.beatty_floor_fiber_card_sets_isBeatty (k := 1) irrational_sqrt_two.inv
      (by simpa only [Nat.cast_one] using hlo) (by simpa only [Nat.cast_one] using hhi)
  refine ⟨γ, δ, ?_, ?_, ?_, ?_⟩
  · rw [← hγ, mem_ofPred_eq, fiber_two, ncard_pair (by decide : (3 : ℕ) ≠ 4)]
    decide
  · rw [← hδ, mem_ofPred_eq, fiber_one, ncard_singleton]
    decide
  · rw [← hγ]
    simp
  · rw [← hδ]
    simp

end MathlibExtTest.NumberTheory.Beatty.FloorFiberSets
