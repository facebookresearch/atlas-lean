/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.StatePriceStochasticDiscountFactor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Tests for state prices and the stochastic discount factor

Two states with `P = ![1/2, 1/2]`, `ψ = ![1/4, 3/4]`, `X = ![2, 4]`: the induced SDF
is `![1/2, 3/2]` and both the state-price value and `E_P[m * X]` equal `7 / 2`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.StatePriceStochasticDiscountFactor

open _root_.MathlibExt.Probability.Finance.StatePriceStochasticDiscountFactor


/-- Example physical probabilities `P = ![1/2, 1/2]`. -/
noncomputable def Pex : Fin 2 → ℝ := ![1/2, 1/2]

/-- Example state prices `ψ = ![1/4, 3/4]`. -/
noncomputable def ψex : Fin 2 → ℝ := ![1/4, 3/4]

/-- Example payoff `X = ![2, 4]`. -/
def Xex : Fin 2 → ℝ := ![2, 4]

theorem sdf_ex_zero : stochasticDiscountFactor ψex Pex 0 = 1 / 2 := by
  simp only [stochasticDiscountFactor, ψex, Pex, Matrix.cons_val_zero]
  norm_num

theorem sdf_ex_one : stochasticDiscountFactor ψex Pex 1 = 3 / 2 := by
  simp only [stochasticDiscountFactor, ψex, Pex, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

theorem price_ex_statePrice : statePriceValue ψex Xex = 7 / 2 := by
  simp only [statePriceValue, ψex, Xex, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

theorem price_ex_expectation :
    physicalExpectation Pex (fun ω => stochasticDiscountFactor ψex Pex ω * Xex ω) = 7 / 2 := by
  simp only [physicalExpectation, stochasticDiscountFactor, Pex, ψex, Xex,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

theorem sdf_ex_pos (ω : Fin 2) : 0 < stochasticDiscountFactor ψex Pex ω := by
  have hψ : ∀ i, 0 < ψex i := by
    intro i
    fin_cases i <;> norm_num [ψex, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hP : ∀ i, 0 < Pex i := by
    intro i
    fin_cases i <;> norm_num [Pex, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact stochasticDiscountFactor_pos hψ hP ω

end MathlibExtTest.Probability.Finance.StatePriceStochasticDiscountFactor
