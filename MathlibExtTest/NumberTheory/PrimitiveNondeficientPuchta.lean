/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.PrimitiveNondeficientPuchta

/-! # Tests for the generalized Puchta lemma -/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- At 6, the least prime is 2 and the first term of the maximum is larger.
example : ∃ p ∈ (6 : ℕ).primeFactors, ((p ^ ((6 : ℕ).factorization p + 1) : ℕ) : ℚ) < 24 := by
  have hn : IsPrimitiveNondeficient 6 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  have hp : 2 ∈ (6 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by decide, by decide⟩
  have hmin : ∀ q ∈ (6 : ℕ).primeFactors, 2 ≤ q :=
    fun _ hq => (Nat.prime_of_mem_primeFactors hq).two_le
  have hH : 2 + (1 / 2 : ℚ) ≤ abundancySup 6 := by
    unfold abundancySup
    decide +kernel
  have hcard : (6 : ℕ).primeFactors.card = 2 := by decide +kernel
  have hB : max (2 * (2 + 2 + 2) / (1 / 2)) (2 * (2 + 1)) = (24 : ℚ) := by
    rw [max_eq_left (by norm_num)]
    norm_num
  simpa only [hcard, Nat.cast_ofNat, hB] using
    exists_pow_factorization_add_one_lt_max 6 2 hn hp hmin (by simp) (1 / 2)
      (by norm_num) (by norm_num) hH

-- The common fixture has prime factors 2, 5, 11, and 13, and supremum 143 / 48.
private theorem puchta1430 (α : ℚ) (hα0 : 0 < α) (hα1 : α < 1) (hH : 2 + α ≤ 143 / 48) :
    ∃ p ∈ (1430 : ℕ).primeFactors,
      ((p ^ ((1430 : ℕ).factorization p + 1) : ℕ) : ℚ) < max (16 / α) 20 := by
  have hn : IsPrimitiveNondeficient 1430 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  have hp : 2 ∈ (1430 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by decide, by decide⟩
  have hmin : ∀ q ∈ (1430 : ℕ).primeFactors, 2 ≤ q :=
    fun _ hq => (Nat.prime_of_mem_primeFactors hq).two_le
  have hsup : abundancySup 1430 = (143 / 48 : ℚ) := by
    unfold abundancySup
    decide +kernel
  have hcard : (1430 : ℕ).primeFactors.card = 4 := by decide +kernel
  have hfirst : 2 * (4 + 2 + 2) = (16 : ℚ) := by norm_num
  have hsecond : 4 * (4 + 1) = (20 : ℚ) := by norm_num
  simpa only [hcard, Nat.cast_ofNat, hfirst, hsecond] using
    exists_pow_factorization_add_one_lt_max 1430 2 hn hp hmin (by simp) α hα0 hα1
      (hsup ▸ hH)

-- At α = 9 / 10, the cardinality term strictly dominates 160 / 9.
example : ∃ p ∈ (1430 : ℕ).primeFactors,
    ((p ^ ((1430 : ℕ).factorization p + 1) : ℕ) : ℚ) < 20 := by
  have hdom : (16 : ℚ) / (9 / 10) < 20 := by norm_num
  simpa only [max_eq_right hdom.le] using
    puchta1430 (9 / 10) (by norm_num) (by norm_num) (by norm_num)

-- At α = 4 / 5, both terms tie, and the conclusion is still strict.
example : ∃ p ∈ (1430 : ℕ).primeFactors,
    ((p ^ ((1430 : ℕ).factorization p + 1) : ℕ) : ℚ) < 20 := by
  have htie : (16 : ℚ) / (4 / 5) = 20 := by norm_num
  simpa only [htie, max_self] using
    puchta1430 (4 / 5) (by norm_num) (by norm_num) (by norm_num)
