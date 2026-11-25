/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MobiusFermatThreeSeven

open ArithmeticFunction MetaMathlibExt

-- At 1 only the empty product contributes. At 63 the extra Fermat factor changes the value.
example : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 ∧ μ 1 = 1 ∧ μ 63 = -4 := by
  have hu : Invertible (fermatUnitFunction 1) := invertibleOne
  obtain ⟨μ, hμ⟩ : ∃ μ : ArithmeticFunction ℤ, μ * fermatUnitFunction = 1 :=
    ⟨_, dirichletInverse_mul_self fermatUnitFunction hu⟩
  refine ⟨μ, hμ, ?_, ?_⟩
  · simpa using (mobiusFermat_three_pow_mul_seven_pow μ hμ 0 0).1
  · have h := (mobiusFermat_three_pow_mul_seven_pow μ hμ 2 1).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    exact_mod_cast h
