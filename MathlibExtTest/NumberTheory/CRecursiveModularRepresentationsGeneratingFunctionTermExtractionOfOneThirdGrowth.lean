/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CRecursiveModularRepresentationsGeneratingFunctionTermExtractionOfOneThirdGrowth

/-! # Tests for term extraction under cube-root growth -/

namespace MathlibExtTest.NumberTheory.CRecursiveModularRepresentationsGeneratingFunctionTermExtractionOfOneThirdGrowth

open MetaMathlibExt

-- The extracted term is below the modulus.
example (t : ℕ → ℕ) (c n : ℕ) (hc : 8 ≤ c)
    (hconv : Summable (fun k : ℕ => (t k : ℝ) * ((c : ℝ)⁻¹) ^ k))
    (hbound : ∀ n, 1 ≤ n → (t n : ℝ) < (c : ℝ) ^ ((n : ℝ) / 3))
    (hn : 1 ≤ n) : t n < c ^ n := by
  have h := generating_function_term_extraction_of_one_third_growth t c hc hconv hbound n hn
  rw [h]
  exact Nat.mod_lt _ (pow_pos (by omega) _)

-- The zero sequence at `c = 8` and `n = 1`.
example : (0 : ℕ) = Nat.floor ((8 : ℝ) ^ (1 ^ 2) *
    (∑' k : ℕ, ((0 : ℕ) : ℝ) * ((((8 : ℝ) ^ 1)⁻¹)) ^ k)) % 8 ^ 1 := by
  have hconv : Summable (fun k : ℕ => (((fun _ => (0 : ℕ)) k : ℕ) : ℝ) * (((8 : ℝ))⁻¹) ^ k) := by
    simp
  have hbound : ∀ (m : ℕ), 1 ≤ m → ((((fun _ => (0 : ℕ)) m : ℕ)) : ℝ) < (8 : ℝ) ^ ((m : ℝ) / 3) := by
    intro m _
    simpa using Real.rpow_pos_of_pos (show (0 : ℝ) < 8 by norm_num) ((m : ℝ) / 3)
  have h := generating_function_term_extraction_of_one_third_growth (fun _ => (0 : ℕ)) 8 (by decide)
    hconv hbound 1 (by decide)
  exact h

end MathlibExtTest.NumberTheory.CRecursiveModularRepresentationsGeneratingFunctionTermExtractionOfOneThirdGrowth
