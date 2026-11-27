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


-- The nonzero sequence `2, 1, 3, 7, 0, 0, …` at `c = 8` and `n = 1`: the scaled value is
-- `1119 / 64`, so the floor is `17`, with a nonzero prefix and a nonzero tail, and its
-- remainder modulo `8` is `t 1 = 1`.
example : Nat.floor ((8 : ℝ) ^ (1 ^ 2) *
    (∑' k : ℕ, (([2, 1, 3, 7].getD k 0 : ℕ) : ℝ) * (((8 : ℝ) ^ 1)⁻¹) ^ k)) % 8 ^ 1 = 1 := by
  have hconv : Summable (fun k : ℕ => (([2, 1, 3, 7].getD k 0 : ℕ) : ℝ) * ((8 : ℝ)⁻¹) ^ k) := by
    apply summable_of_ne_finset_zero (s := Finset.range 4)
    intro k hk
    have hk4 : [2, 1, 3, 7].length ≤ k := by simpa using hk
    simp [List.getElem?_eq_none hk4]
  have hbound : ∀ m, 1 ≤ m → (([2, 1, 3, 7].getD m 0 : ℕ) : ℝ) < (8 : ℝ) ^ ((m : ℝ) / 3) := by
    intro m hm
    have h8 : (8 : ℝ) ^ ((m : ℝ) / 3) = 2 ^ m := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
        show (3 : ℝ) * ((m : ℝ) / 3) = m by ring, Real.rpow_natCast]
    rw [h8]
    rcases m with _ | _ | _ | _ | m
    · omega
    · norm_num
    · norm_num
    · norm_num
    · simp
  have h := generating_function_term_extraction_of_one_third_growth
    (fun k => [2, 1, 3, 7].getD k 0) 8 (by decide) hconv hbound 1 le_rfl
  exact h.symm

end MathlibExtTest.NumberTheory.CRecursiveModularRepresentationsGeneratingFunctionTermExtractionOfOneThirdGrowth
