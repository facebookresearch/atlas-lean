/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.GilbertVarshamov

open MathlibExt.Combinatorics.Coding.GilbertVarshamov

-- Binary codes of length 3 and minimum distance 2: some code has at least 2^3 / 4 = 2 words.
example : ∃ C : Finset (Fin 3 → Bool),
    (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 ≤ hammingDist c₁ c₂) ∧ 2 ≤ C.card := by
  obtain ⟨C, hC, hcount⟩ := exists_code_pow_le_card_mul_sum (α := Bool) 3 (d := 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  simp [Finset.sum_range_succ] at hcount
  omega

-- Boundary `d = 1`: every word may be taken, and the bound reads `q ^ n ≤ |C|`.
example : ∃ C : Finset (Fin 2 → Fin 3),
    (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 1 ≤ hammingDist c₁ c₂) ∧ 9 ≤ C.card := by
  obtain ⟨C, hC, hcount⟩ := exists_code_pow_le_card_mul_sum (α := Fin 3) 2 (d := 1) le_rfl
  exact ⟨C, hC, by simpa using hcount⟩

-- The covering property of a maximal code: the whole space, with `d = 1`.
example : (Finset.univ : Finset (Fin 2 → Bool)).biUnion (fun c => Hamming.ball c (1 - 1)) =
    Finset.univ :=
  biUnion_ball_eq_univ_of_maximal _ fun v _ => Finset.mem_univ v

-- The rate form is not vacuous: binary, `δ = 1/4`, `n = 4`, `d = 2`.
example : ∃ C : Finset (Fin 4 → Bool),
    (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 ≤ hammingDist c₁ c₂) ∧
    Real.exp (4 * (Real.log 2 - Real.qaryEntropy 2 (1 / 4))) ≤ C.card := by
  have h := exists_code_exp_le_card (α := Bool) (by simp) (δ := 1 / 4) (by norm_num)
    (by simp; norm_num) 4 (d := 2) (by norm_num) (by norm_num)
  simpa using h
