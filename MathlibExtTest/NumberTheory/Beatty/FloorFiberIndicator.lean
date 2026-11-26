/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.FloorFiberIndicator

namespace MetaMathlibExt.beatty_floor_fiber_card_eq_add_indicator

open Set Real

-- Each value of `⌊nα⌋` is taken by `k` or by `k + 1` positive integers `n`.
example {α : ℝ} {k : ℕ} (hirr : Irrational α) (h1 : 1 / ((k : ℝ) + 1) < α)
    (h2 : α < 1 / (k : ℝ)) (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k ∨
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * α⌋ = t}.ncard = k + 1 := by
  obtain ⟨δ, -, h⟩ := beatty_floor_fiber_card_eq_add_indicator hirr h1 h2
  rw [h t]
  by_cases ht : (t : ℤ) ∈ {beattySeq δ m | m > 0}
  · exact Or.inr (by rw [indicator_of_mem ht, Pi.one_apply])
  · exact Or.inl (by rw [indicator_of_notMem ht, add_zero])

/-- The bounds `7/5 < √2 < 10/7`, enough to locate the first multiples of `√2 - 1`. -/
private theorem sqrt_two_bounds : 7 / 5 < √2 ∧ √2 < 10 / 7 :=
  ⟨(lt_sqrt (by norm_num)).2 (by norm_num), (sqrt_lt' (by norm_num)).2 (by norm_num)⟩

-- For `α = √2 - 1` and `k = 2`, the value `0` is taken only by `n = 1, 2` and the value `2` by
-- `n = 5, 6, 7`, so the Beatty set given by the theorem omits `0` and contains `2`.
example : ∃ δ : ℝ, 0 < δ ∧ (0 : ℤ) ∉ {beattySeq δ m | m > 0} ∧
    (2 : ℤ) ∈ {beattySeq δ m | m > 0} := by
  obtain ⟨hlo, hhi⟩ := sqrt_two_bounds
  have hpos : (0 : ℝ) ≤ √2 - 1 := by linarith
  have hirr : Irrational (√2 - 1) := by
    simpa only [Nat.cast_one] using irrational_sqrt_two.sub_natCast 1
  obtain ⟨δ, hδ, h⟩ := beatty_floor_fiber_card_eq_add_indicator (k := 2) hirr
    (by norm_num; linarith) (by norm_num; linarith)
  have hfib0 : {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (√2 - 1)⌋ = ((0 : ℕ) : ℤ)} = {1, 2} := by
    ext n
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Int.floor_eq_iff]
    push_cast
    constructor
    · rintro ⟨hn, -, h1⟩
      have hn2 : n ≤ 2 := by
        by_contra hlt
        have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
        linarith [mul_le_mul_of_nonneg_right h3 hpos]
      omega
    · rintro (rfl | rfl) <;> refine ⟨by norm_num, ?_, ?_⟩ <;> push_cast <;> linarith
  have hfib2 : {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (√2 - 1)⌋ = ((2 : ℕ) : ℤ)} = {5, 6, 7} := by
    ext n
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, Int.floor_eq_iff]
    push_cast
    constructor
    · rintro ⟨-, h2, h3⟩
      have hn5 : 5 ≤ n := by
        by_contra hlt
        have h4 : (n : ℝ) ≤ 4 := by exact_mod_cast (by omega : n ≤ 4)
        linarith [mul_le_mul_of_nonneg_right h4 hpos]
      have hn7 : n ≤ 7 := by
        by_contra hlt
        have h8 : (8 : ℝ) ≤ n := by exact_mod_cast (by omega : 8 ≤ n)
        linarith [mul_le_mul_of_nonneg_right h8 hpos]
      omega
    · rintro (rfl | rfl | rfl) <;> refine ⟨by norm_num, ?_, ?_⟩ <;> push_cast <;> linarith
  have h0 := h 0
  rw [hfib0, ncard_pair (by norm_num), Nat.cast_zero] at h0
  have h2 := h 2
  rw [hfib2, ncard_eq_three.2 ⟨5, 6, 7, by norm_num, by norm_num, by norm_num, rfl⟩,
    Nat.cast_ofNat] at h2
  refine ⟨δ, hδ, fun hmem ↦ ?_, ?_⟩
  · rw [indicator_of_mem hmem, Pi.one_apply] at h0
    omega
  · by_contra hmem
    rw [indicator_of_notMem hmem] at h2
    omega

end MetaMathlibExt.beatty_floor_fiber_card_eq_add_indicator
