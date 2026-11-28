/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRho

/-! # Tests for the combinatorial formula for the `k`-Padovan–Perrin numbers -/

namespace MathlibExtTest.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRho

open MetaMathlibExt

private theorem init_zero : padovanPerrinFundamental (1 : ℤ) 2 1 2 3 0 = 0 := by
  rw [padovanPerrinFundamental_of_lt (1 : ℤ) 2 1 2 3 0 (by omega)]
  decide

private theorem init_one : padovanPerrinFundamental (1 : ℤ) 2 1 2 3 1 = 0 := by
  rw [padovanPerrinFundamental_of_lt (1 : ℤ) 2 1 2 3 1 (by omega)]
  decide

private theorem init_two : padovanPerrinFundamental (1 : ℤ) 2 1 2 3 2 = 1 := by
  rw [padovanPerrinFundamental_of_lt (1 : ℤ) 2 1 2 3 2 (by omega)]
  decide

private theorem rho_two : padovanPerrinRho (1 : ℤ) 2 1 2 2 = 0 := by
  decide

private theorem rho_three : padovanPerrinRho (1 : ℤ) 2 1 2 3 = 1 := by
  decide

private theorem rho_four : padovanPerrinRho (1 : ℤ) 2 1 2 4 = 0 := by
  decide

private theorem rho_five : padovanPerrinRho (1 : ℤ) 2 1 2 5 = 1 := by
  decide

-- With `k = 2` and initial values `(0, 0, 1)`, the formula gives `v 4 = 1`.
example : padovanPerrinFundamental (1 : ℤ) 2 1 2 3 4 = 1 := by
  have hv := padovanPerrinFundamental_isSolution (1 : ℤ) 2 1 2 3
  have h := kPadovanPerrin_eq_sum_rho (2 : ℤ) _ hv 4 (by omega)
  have e1 : (4 : ℕ) - 1 = 3 := by omega
  have e2 : (4 : ℕ) - 2 = 2 := by omega
  rw [e1, e2, init_zero, init_one, init_two, rho_two, rho_three, rho_four] at h
  simpa using h

-- At `n = 5` the same instance gives `v 5 = 2`.
example : padovanPerrinFundamental (1 : ℤ) 2 1 2 3 5 = 2 := by
  have hv := padovanPerrinFundamental_isSolution (1 : ℤ) 2 1 2 3
  have h := kPadovanPerrin_eq_sum_rho (2 : ℤ) _ hv 5 (by omega)
  have e1 : (5 : ℕ) - 1 = 4 := by omega
  have e2 : (5 : ℕ) - 2 = 3 := by omega
  rw [e1, e2, init_zero, init_one, init_two, rho_three, rho_four, rho_five] at h
  simpa using h

end MathlibExtTest.NumberTheory.GeneralizedPadovanPerrinModelKPadovanPerrinEqSumRho
