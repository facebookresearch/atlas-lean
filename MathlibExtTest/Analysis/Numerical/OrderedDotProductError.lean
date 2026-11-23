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

/-- A two-term instance with asymmetric data, computed exactly:
`h = ![1, 2]`, `dh = ![1/2, 0]`, `x = ![3, 4]`, `dx = ![1/4, 0]`,
no product or accumulation error. The perturbed products are
`3/2 * 13/4 = 39/8` and `2 * 4 = 8`, so the perturbed output is
`103/8` and the ideal output is `1 * 3 + 2 * 4 = 11`. -/
example : outputPerturbed 2 ![1, 2] ![1 / 2, 0] ![3, 4] ![1 / 4, 0]
      ![0, 0] ![0, 0] = 103 / 8 := by
  norm_num [outputPerturbed, accumulator, extend, productPerturbed,
    inputPerturbed, coeffPerturbed]

example : outputIdeal 2 ![1, 2] ![3, 4] = 11 := by
  norm_num [outputIdeal, Fin.sum_univ_two]

/-- The fold equals the sum, in an asymmetric instance. -/
example : accumulator (extend 2 ![39 / 8, 8]) (extend 2 ![0, 0]) 2
    = ∑ k : Fin 2, (![39 / 8, 8] k + ![0, 0] k) :=
  accumulator_extend_eq_sum 2 ![39 / 8, 8] ![0, 0]

/-- The error bound on the same instance, applied in the model's
argument order (`h dh x dx dp da`). With `ex = 1/4`, `eh = 1/2` and
`ep = ea = 0` the bound is
`1/4 * 3 + 1/2 * 7 + 2 * (1/2) * (1/4) = 9/2`, and the actual error
is `103/8 - 11 = 15/8`. -/
example : |outputPerturbed 2 ![1, 2] ![1 / 2, 0] ![3, 4] ![1 / 4, 0]
      ![0, 0] ![0, 0] - outputIdeal 2 ![1, 2] ![3, 4]|
    ≤ (1 / 4) * (∑ k : Fin 2, |![1, 2] k|)
      + (1 / 2) * (∑ k : Fin 2, |![3, 4] k|)
      + (2 : ℝ) * (1 / 2) * (1 / 4) + (2 : ℝ) * 0 + (2 : ℝ) * 0 :=
  orderedDotProduct_error_bound 2 ![1, 2] ![1 / 2, 0] ![3, 4] ![1 / 4, 0]
    ![0, 0] ![0, 0] (1 / 4) (1 / 2) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro k; fin_cases k <;> norm_num)
    (by intro k; fin_cases k <;> norm_num)
    (by intro k; fin_cases k <;> norm_num)
    (by intro k; fin_cases k <;> norm_num)

/-- The per-product expansion keeps the cross term: with
`h = 1`, `x = 3`, `dh = 1/2`, `dx = 1/4`, `dp = 0`, the product
error is `3/2 * 13/4 - 3 = 15/8 = 1/4 + 3/2 + 1/8`, the last term
being `dh * dx = 1/8`. -/
example : productPerturbed 2 ![1, 2] ![1 / 2, 0] ![3, 4] ![1 / 4, 0]
      ![0, 0] 0 - ![1, 2] 0 * ![3, 4] 0 = 15 / 8 := by
  norm_num [productPerturbed, inputPerturbed, coeffPerturbed]

end MathlibExtTest.Analysis.Numerical.OrderedDotProductError
