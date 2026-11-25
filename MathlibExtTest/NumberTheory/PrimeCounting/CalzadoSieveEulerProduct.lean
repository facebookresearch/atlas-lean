/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.PrimeCounting.CalzadoSieveEulerProduct

open Finset MetaMathlibExt

-- The same constants work for the empty product at 2 and the single factor at 5/2.
example (P : Set ℕ) [DecidablePred (· ∈ P)] (ω : ℕ → ℝ) (k : ℝ) (hk : 0 < k)
    (hP : ∀ p ∈ P, p.Prime ∧ 0 ≤ ω p ∧ ω p < p) (h2 : 2 ∈ P)
    (hdim : ∃ C₀ : ℝ, ∀ t z : ℝ, 2 ≤ t → t ≤ z →
      |∑ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p ∈ P ∧ t ≤ (p : ℝ) ∧ (p : ℝ) < z),
          ω p * Real.log p / p - k * Real.log (z / t)| ≤ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c / Real.log 2 ^ k ≤ 1 ∧ 1 ≤ C / Real.log 2 ^ k ∧
      c / Real.log (5 / 2) ^ k ≤ 1 - ω 2 / 2 ∧
      1 - ω 2 / 2 ≤ C / Real.log (5 / 2) ^ k := by
  have hcut₂ :
      (range ⌈(2 : ℝ)⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < 2) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp₂ := (hP p (mem_filter.mp hp).2.1).1.two_le
    exact (not_lt_of_ge (by exact_mod_cast hp₂)) (mem_filter.mp hp).2.2
  have hceil : ⌈(5 / 2 : ℝ)⌉₊ = 3 := by
    apply le_antisymm (Nat.ceil_le.mpr (by norm_num))
    exact Nat.lt_ceil.mpr (by norm_num : ((2 : ℕ) : ℝ) < 5 / 2)
  have hcut₅ :
      (range ⌈(5 / 2 : ℝ)⌉₊).filter (fun p : ℕ => p ∈ P ∧ (p : ℝ) < 5 / 2) = {2} := by
    ext p
    simp only [hceil, mem_filter, mem_range, mem_singleton]
    constructor
    · intro hp
      have := (hP p hp.2.1).1.two_le
      omega
    · rintro rfl
      norm_num [h2]
  obtain ⟨c, C, hc, hC, h⟩ := calzado_sieve_euler_product_asymp P ω k (hk := hk) hP hdim
  have hlo := h 2 le_rfl
  have hhi := h (5 / 2) (by norm_num)
  rw [hcut₂, prod_empty] at hlo
  rw [hcut₅, prod_singleton, Nat.cast_ofNat] at hhi
  exact ⟨c, C, hc, hC, hlo.1, hlo.2, hhi.1, hhi.2⟩
