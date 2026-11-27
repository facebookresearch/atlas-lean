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

-- When the cardinality term dominates, the bound is strictly below that term.
example (n p₁ : ℕ) (hn : IsPrimitiveNondeficient n) (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) (hne : ¬ (p₁ = 3 ∧ n.primeFactors.card = 3))
    (α : ℚ) (hα0 : 0 < α) (hα1 : α < 1) (hH : 2 + α ≤ abundancySup n)
    (hdom : 2 * ((n.primeFactors.card : ℚ) + 2 + p₁) / α ≤
      (n.primeFactors.card : ℚ) * ((n.primeFactors.card : ℚ) + 1)) :
    ∃ p ∈ n.primeFactors, ((p ^ (n.factorization p + 1) : ℕ) : ℚ) <
      (n.primeFactors.card : ℚ) * ((n.primeFactors.card : ℚ) + 1) := by
  simpa only [max_eq_right hdom] using
    exists_pow_factorization_add_one_lt_max n p₁ hn hp₁ hmin hne α hα0 hα1 hH
