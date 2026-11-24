/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MobiusFermat

open ArithmeticFunction MetaMathlibExt

-- The unit function distinguishes a generator from the product of two generators.
example : fermatUnitFunction 0 = 0 ∧ fermatUnitFunction 31 = 1 ∧ fermatUnitFunction 21 = 0 := by
  decide

-- Six has a Fermat generator as a divisor, but every element of the semigroup is odd.
example : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 ∧
    let weighted := (μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log
    μ 1 = 1 ∧ weighted 1 = 0 ∧ μ 6 = 0 ∧ weighted 6 = 0 := by
  have hunit : Invertible (fermatUnitFunction 1) := invertibleOne
  have hinv := dirichletInverse_mul_self fermatUnitFunction hunit
  obtain ⟨hμ1, hΛ1, hoff⟩ := mobiusFermat_one_and_vanishing _ hinv
  refine ⟨_, hinv, hμ1, hΛ1, hoff 6 ?_⟩
  intro h
  have : Odd (6 : ℕ) := by
    refine Submonoid.closure_induction (motive := fun x _ => Odd x) ?_ odd_one
      (fun _ _ _ _ ha hb => ha.mul hb) h
    rintro _ ⟨n, hn, rfl⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one
  exact (by decide : ¬ Odd (6 : ℕ)) this
