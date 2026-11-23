/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.WeightedColoring

open Finset
open scoped BigOperators

namespace MathlibExtTest.WeightedColoring

private def sparseCapacity : Matrix (Fin 768) (Fin 768) ℕ := fun a b =>
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 2
  else if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 5
  else 0

private theorem sparseCapacity_isSymm : sparseCapacity.IsSymm := by
  change Matrix.transpose sparseCapacity = sparseCapacity
  ext a b
  change sparseCapacity b a = sparseCapacity a b
  simp only [sparseCapacity]
  split_ifs <;> aesop

private theorem sparseCapacity_row_sum (a : Fin 768) :
    ∑ b, sparseCapacity a b =
      (if a = 0 then 2 else 0) + (if a = 1 then 2 else 0) +
        (if a = 2 then 5 else 0) + (if a = 3 then 5 else 0) := by
  by_cases h0 : a = 0
  · subst a
    simp [sparseCapacity]
  by_cases h1 : a = 1
  · subst a
    simp [sparseCapacity]
  by_cases h2 : a = 2
  · subst a
    simp [sparseCapacity]
  by_cases h3 : a = 3
  · subst a
    simp [sparseCapacity]
  · simp [sparseCapacity, h0, h1, h2, h3]

private theorem sparseCapacity_row_bound (a : Fin 768) :
    ∑ b, sparseCapacity a b ≤ 5 := by
  rw [sparseCapacity_row_sum]
  split_ifs <;> omega

private theorem sparseCapacity_diagonal (a : Fin 768) : sparseCapacity a a = 0 := by
  simp only [sparseCapacity]
  by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;>
    by_cases h2 : a = 2 <;> by_cases h3 : a = 3 <;> simp_all

private theorem sparseCapacity_total :
    ∑ a, ∑ b, sparseCapacity a b = 14 := by
  rw [sum_congr rfl fun a _ => sparseCapacity_row_sum a]
  simp only [sum_add_distrib, Fintype.sum_ite_eq']

private theorem sparseCapacity_offDiagonal_total :
    ∑ a, ∑ b with b ≠ a, sparseCapacity a b = 14 := by
  rw [← sparseCapacity_total]
  apply sum_congr rfl
  intro a _
  rw [sum_filter]
  apply sum_congr rfl
  intro b _
  by_cases hba : b = a
  · subst b
    simp [sparseCapacity_diagonal]
  · simp [hba]

private theorem sparseCapacity_offDiagonal_row_bound (a : Fin 768) :
    ∑ b with b ≠ a, sparseCapacity a b ≤ 5 := by
  rw [sum_filter]
  calc
    (∑ b, if b ≠ a then sparseCapacity a b else 0) ≤
        ∑ b, sparseCapacity a b := by
      gcongr with b
      split_ifs <;> simp
    _ ≤ 5 := sparseCapacity_row_bound a

-- Exact source threshold `3 * 2 ^ 8 = 768`, with nonzero sparse weights and total weight 14.
example : ∃ χ : Fin 768 → Fin 2,
    (∀ γ, 2 * #{a | χ a = γ} < 2 * 768) ∧
      ∀ γ γ', γ ≠ γ' →
        2 ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', sparseCapacity a b) ≤
          2 * 14 + 768 * 5 := by
  simpa only [Fintype.card_fin, sparseCapacity_offDiagonal_total] using
    Matrix.exists_balanced_coloring_fin (K := 2) (g := 768) (by norm_num) (by norm_num)
      sparseCapacity sparseCapacity_isSymm 5 sparseCapacity_offDiagonal_row_bound

-- The zero-capacity and zero-row-bound boundary remains nonvacuous at the source threshold.
example : ∃ χ : Fin 768 → Fin 2,
    (∀ γ, 2 * #{a | χ a = γ} < 2 * 768) ∧
      ∀ γ γ', γ ≠ γ' →
        2 ^ 3 * (∑ a with χ a = γ,
          ∑ b with χ b = γ', (0 : Matrix (Fin 768) (Fin 768) ℕ) a b) ≤
          2 * (∑ a, ∑ b with b ≠ a, (0 : Matrix (Fin 768) (Fin 768) ℕ) a b) +
            768 * 0 := by
  exact Matrix.exists_balanced_coloring_fin (by norm_num) (by norm_num) 0 (by simp) 0 (by simp)

-- For one color the core threshold is sharp: `4 * 1 ^ 6 + 1 ^ 2 < 6`.
example : ∃ χ : Fin 6 → Fin 1,
    (∀ γ, 1 * #{a | χ a = γ} < 2 * 6) ∧
      ∀ γ γ',
        1 ^ 3 * (∑ a with χ a = γ,
          ∑ b with χ b = γ', (0 : Matrix (Fin 6) (Fin 6) ℕ) a b) ≤
          1 * (∑ a, ∑ b, (0 : Matrix (Fin 6) (Fin 6) ℕ) a b) + 6 * 0 := by
  exact Matrix.exists_balanced_coloring (c := (0 : Matrix (Fin 6) (Fin 6) ℕ))
    (by simp) (by simp) 0 (by simp) (by norm_num) (by norm_num)

private def diagonalCapacity : Matrix (Fin 768) (Fin 768) ℕ := fun a b =>
  if a = b then 7 else 0

private theorem diagonalCapacity_isSymm : diagonalCapacity.IsSymm := by
  change Matrix.transpose diagonalCapacity = diagonalCapacity
  ext a b
  change diagonalCapacity b a = diagonalCapacity a b
  simp [diagonalCapacity, eq_comm]

example : diagonalCapacity 0 0 = 7 := by simp [diagonalCapacity]

-- Arbitrary nonzero diagonal entries are ignored by the off-diagonal theorem.
example : ∃ χ : Fin 768 → Fin 2,
    (∀ γ, 2 * #{a | χ a = γ} < 2 * 768) ∧
      ∀ γ γ', γ ≠ γ' →
        2 ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', diagonalCapacity a b) ≤ 0 := by
  simpa [diagonalCapacity] using
    Matrix.exists_balanced_coloring_fin (K := 2) (g := 768) (by norm_num) (by norm_num)
      diagonalCapacity diagonalCapacity_isSymm 0 (by simp [diagonalCapacity])

section BetaBound

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι

-- The source beta bound is recovered from the public theorem using standard natural division.
example (c : Matrix ι ι ℕ) (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g) (hs : c.IsSymm)
    (P : ℕ) (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : ι → κ, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' →
        (∑ a with χ a = γ, ∑ b with χ b = γ', c a b) ≤
          max 1 ((K * (∑ a, ∑ b with b ≠ a, c a b) + g * P) / K ^ 3) := by
  obtain ⟨χ, hclass, hblock⟩ :=
    Matrix.exists_balanced_coloring_offDiagonal c hK hg hs P hP
  refine ⟨χ, hclass, fun γ γ' hne => le_max_of_le_right ?_⟩
  apply (Nat.le_div_iff_mul_le (pow_pos (by omega) 3)).2
  rw [mul_comm]
  exact hblock γ γ' hne

end BetaBound

#print axioms Matrix.exists_balanced_coloring
#print axioms Matrix.exists_balanced_coloring_offDiagonal
#print axioms Matrix.exists_balanced_coloring_fin

end MathlibExtTest.WeightedColoring
