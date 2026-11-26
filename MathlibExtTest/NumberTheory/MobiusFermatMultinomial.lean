/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MobiusFermatMultinomial

/-! # Tests for the multinomial formula for the Möbius–Fermat function -/

open ArithmeticFunction MetaMathlibExt

-- The empty product has value one for a Dirichlet inverse that exists.
example : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 ∧ (μ 1 : ℚ) = 1 := by
  have hu : Invertible (fermatUnitFunction 1) := invertibleOne
  obtain ⟨μ, hμ⟩ : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 :=
    ⟨_, dirichletInverse_mul_self fermatUnitFunction hu⟩
  exact ⟨μ, hμ, by simpa using mobiusFermat_eq_multinomial μ hμ 0 (by simp) (by simp)⟩

-- An exponent above one at index two is allowed when index three is absent.
example (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) : (μ 9 : ℚ) = 1 := by
  have h := mobiusFermat_eq_multinomial μ hμ (Finsupp.single 2 2)
    (by simp) (Or.inr (by simp))
  norm_num [Finsupp.prod_single_index, Finsupp.sum_single_index, Nat.factorial] at h
  exact_mod_cast h

-- Both small indices can occur when the exponent at index two is exactly one.
example (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) : (μ 147 : ℚ) = -3 := by
  have h := mobiusFermat_eq_multinomial μ hμ (Finsupp.single 2 1 + Finsupp.single 3 2)
    (by
      intro n hn
      have hn' := Finsupp.support_add hn
      simp at hn'
      rcases hn' with rfl | rfl <;> decide)
    (Or.inl (by simp))
  have hd : Disjoint (Finsupp.single 2 (1 : ℕ)).support (Finsupp.single 3 (2 : ℕ)).support := by
    simp
  simp only [Finsupp.prod_add_index_of_disjoint hd, Finsupp.sum_add_index_of_disjoint hd] at h
  norm_num [Finsupp.prod_single_index, Finsupp.sum_single_index, Nat.factorial] at h
  exact h

-- The integer 63 divides 1575, but its complementary factor 25 is outside the semigroup.
-- In the admissible factorization 7 * 15², the exceptional generator does not contribute.
example (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) : (μ 1575 : ℚ) = -3 := by
  have h := mobiusFermat_eq_multinomial μ hμ (Finsupp.single 3 1 + Finsupp.single 4 2)
    (by
      intro n hn
      have hn' := Finsupp.support_add hn
      simp at hn'
      rcases hn' with rfl | rfl <;> decide)
    (Or.inl (by simp))
  have hd : Disjoint (Finsupp.single 3 (1 : ℕ)).support (Finsupp.single 4 (2 : ℕ)).support := by
    simp
  simp only [Finsupp.prod_add_index_of_disjoint hd, Finsupp.sum_add_index_of_disjoint hd] at h
  norm_num [Finsupp.prod_single_index, Finsupp.sum_single_index, Nat.factorial] at h
  exact h
