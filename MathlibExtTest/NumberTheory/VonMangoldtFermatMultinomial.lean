/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.VonMangoldtFermatMultinomial

open ArithmeticFunction MetaMathlibExt

-- The inverse exists and the empty product contributes zero.
example : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 ∧
    ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log) 1 = 0 := by
  have hu : Invertible (fermatUnitFunction 1) := invertibleOne
  obtain ⟨μ, hμ⟩ : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 :=
    ⟨_, dirichletInverse_mul_self fermatUnitFunction hu⟩
  have h := vonMangoldtFermat_eq_multinomial μ hμ 0 (by simp) (by simp)
  exact ⟨μ, hμ, by
    simpa only [Finsupp.prod_zero_index, Nat.cast_one, Real.log_one, mul_zero] using h⟩

-- Two factors of three and no seven give the coefficient -1/2.
example (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) :
    ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log) 9 =
      -(Real.log 9 / 2) := by
  have h := vonMangoldtFermat_eq_multinomial μ hμ (Finsupp.single 2 2)
    (by simp) (Or.inr (by simp))
  norm_num only [Finsupp.prod_single_index, Finsupp.sum_single_index, pow_zero, Nat.factorial] at h
  linarith only [h]

-- When three has multiplicity one, seven can occur repeatedly.
example (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) :
    ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log) 147 =
      Real.log 147 := by
  have h := vonMangoldtFermat_eq_multinomial μ hμ (Finsupp.single 2 1 + Finsupp.single 3 2)
    (by
      intro n hn
      have hn' := Finsupp.support_add hn
      simp at hn'
      rcases hn' with rfl | rfl <;> decide)
    (Or.inl (by simp))
  have hd : Disjoint (Finsupp.single 2 (1 : ℕ)).support (Finsupp.single 3 (2 : ℕ)).support := by
    simp
  simp only [Finsupp.prod_add_index_of_disjoint hd, Finsupp.sum_add_index_of_disjoint hd] at h
  norm_num only [Finsupp.prod_single_index, Finsupp.sum_single_index, pow_zero, Nat.factorial] at h
  simpa only [one_mul] using h
