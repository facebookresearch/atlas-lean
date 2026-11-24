/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinExpansion

/-! # Tests for the expansion in the Padovan–Perrin fundamental system -/

open MetaMathlibExt

-- Order zero: for `s = p = 0` the sum is empty, so every solution vanishes.
example (k₁ k₂ : ℤ) (v : ℕ → ℤ) (hv : (padovanPerrinRecurrence k₁ k₂ 0 0).IsSolution v)
    (n : ℕ) : v n = 0 := by
  simpa using padovanPerrin_eq_sum_fundamental k₁ k₂ 0 0 v hv n

-- For `v (n + 3) = k₁ v (n + 1) + k₂ v n` (`p = 1`, `s = 2`) the three fundamental sequences
-- take the values `0`, `k₂`, `k₁` at `4`, so `v 4 = k₂ v 1 + k₁ v 2`.
example (k₁ k₂ : ℤ) (v : ℕ → ℤ) (hv : (padovanPerrinRecurrence k₁ k₂ 1 2).IsSolution v) :
    v 4 = k₂ * v 1 + k₁ * v 2 := by
  have hf (j : ℕ) : padovanPerrinFundamental k₁ k₂ 1 2 j 4 =
      k₁ * padovanPerrinFundamental k₁ k₂ 1 2 j 2 + k₂ * padovanPerrinFundamental k₁ k₂ 1 2 j 1 :=
    (padovanPerrinRecurrence_isSolution_iff k₁ k₂ 1 2 two_pos _).1
      (padovanPerrinFundamental_isSolution k₁ k₂ 1 2 j) 1
  rw [padovanPerrin_eq_sum_fundamental k₁ k₂ 1 2 v hv 4]
  simp [Finset.sum_range_succ, hf, padovanPerrinFundamental_of_lt]
  ring

-- For `s = 0` the coefficient `k₁` never enters: with `p = 2` the recurrence reads
-- `v (n + 2) = k₂ v n`, and the expansion gives `v 2 = k₂ v 0`.
example (k₁ k₂ : ℤ) (v : ℕ → ℤ) (hv : (padovanPerrinRecurrence k₁ k₂ 2 0).IsSolution v) :
    v 2 = k₂ * v 0 := by
  have hf (j : ℕ) : padovanPerrinFundamental k₁ k₂ 2 0 j 2 =
      k₂ * padovanPerrinFundamental k₁ k₂ 2 0 j 0 := by
    have h := padovanPerrinFundamental_isSolution k₁ k₂ 2 0 j 0
    change padovanPerrinFundamental k₁ k₂ 2 0 j 2 = ∑ i : Fin 2,
      ((if (i : ℕ) = 0 then k₂ else 0) + (if (i : ℕ) = 2 then k₁ else 0)) *
        padovanPerrinFundamental k₁ k₂ 2 0 j (0 + i) at h
    simpa [Fin.sum_univ_two] using h
  rw [padovanPerrin_eq_sum_fundamental k₁ k₂ 2 0 v hv 2]
  simp [hf, padovanPerrinFundamental_of_lt]
  ring
