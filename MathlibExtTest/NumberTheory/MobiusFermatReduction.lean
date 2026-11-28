/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MobiusFermatReduction

open ArithmeticFunction MetaMathlibExt

-- Keep 63 = 3² · 7 in the base and replace two copies of 15 by 31 and 127.
example : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 ∧ μ 14175 * 2 = μ 248031 := by
  have hu : Invertible (fermatUnitFunction 1) := invertibleOne
  obtain ⟨μ, hμ⟩ : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 :=
    ⟨_, dirichletInverse_mul_self fermatUnitFunction hu⟩
  refine ⟨μ, hμ, ?_⟩
  have h := mobiusFermat_mul_factorial_eq_squarefree_part _ hμ 2 1 (Finsupp.single 4 2)
    (by simp) {5, 7} (by decide) (by simp)
  norm_num [Finset.prod_insert, Nat.factorial] at h
  exact h
