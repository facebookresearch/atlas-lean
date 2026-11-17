/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Analysis.Numerical.OrderedDotProductError
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open MathlibExt.Analysis.Numerical.OrderedDotProductError

namespace MathlibExtTest.Analysis.Numerical.OrderedDotProductError

/-- A two-term instance computed exactly: perturbed inputs and
coefficients `3/2`, ideal inputs and coefficients `1`, so the
perturbed output is `9/2`, the ideal output is `2`, and the error is
`5/2`. -/
example : outputPerturbed 2 ![1, 1] ![1 / 2, 1 / 2] ![1, 1] ![1 / 2, 1 / 2]
      ![0, 0] ![0, 0] = 9 / 2 := by
  norm_num [outputPerturbed, accumulator, extend, productPerturbed,
    inputPerturbed, coeffPerturbed]

example : outputIdeal 2 ![1, 1] ![1, 1] = 2 := by
  norm_num [outputIdeal, Fin.sum_univ_two]

/-- The fold equals the sum, in the same instance. -/
example : accumulator (extend 2 ![3 / 2, 3 / 2]) (extend 2 ![0, 0]) 2
    = ∑ k : Fin 2, (![3 / 2, 3 / 2] k + ![0, 0] k) :=
  accumulator_extend_eq_sum 2 ![3 / 2, 3 / 2] ![0, 0]

/-- The error bound on the same instance. With `ex = eh = 1/2` and
`ep = ea = 0` the bound is
`1/2 * 2 + 1/2 * 2 + 2 * (1/2) * (1/2) = 5/2`, so the bound is met
with equality: it is not vacuous, and the cross term contributes
`1/2` of it. -/
example : |outputPerturbed 2 ![1, 1] ![1 / 2, 1 / 2] ![1, 1] ![1 / 2, 1 / 2]
      ![0, 0] ![0, 0] - outputIdeal 2 ![1, 1] ![1, 1]|
    ≤ (1 / 2) * (∑ k : Fin 2, |![1, 1] k|)
      + (1 / 2) * (∑ k : Fin 2, |![1, 1] k|)
      + (2 : ℝ) * (1 / 2) * (1 / 2) + (2 : ℝ) * 0 + (2 : ℝ) * 0 :=
  orderedDotProduct_error_bound 2 ![1, 1] ![1, 1] ![1 / 2, 1 / 2] ![1 / 2, 1 / 2]
    ![0, 0] ![0, 0] (1 / 2) (1 / 2) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro k; fin_cases k <;> norm_num)
    (by intro k; fin_cases k <;> norm_num)
    (by intro k; fin_cases k <;> norm_num)
    (by intro k; fin_cases k <;> norm_num)

/-- The per-product expansion keeps the cross term: with
`h = x = 1`, `dh = dx = 1/2`, `dp = 0`, the product error is
`3/2 * 3/2 - 1 = 5/4 = 1/2 + 1/2 + 1/4`, the last term being
`dh * dx`. -/
example : productPerturbed 2 ![1, 1] ![1 / 2, 1 / 2] ![1, 1] ![1 / 2, 1 / 2]
      ![0, 0] 0 - ![1, 1] 0 * ![1, 1] 0 = 5 / 4 := by
  norm_num [productPerturbed, inputPerturbed, coeffPerturbed]

end MathlibExtTest.Analysis.Numerical.OrderedDotProductError
