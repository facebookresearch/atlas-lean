/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Perm.IntegralConvolution
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Binary signed convolution

The four binary labelings give three identity terms and one negative transposition term.
The positive parameter two reverses both coefficients in the lambda element. Empty words
and empty alphabets exercise the two different zero boundaries.
-/

noncomputable section

namespace BinaryConvolutionTests

open Equiv.Perm
open scoped BigOperators

private theorem binary_sort (a b : Fin 2) :
    Tuple.sort ![a, b] = if a ≤ b then 1 else Equiv.swap (0 : Fin 2) 1 := by
  fin_cases a <;> fin_cases b
  all_goals
    apply Eq.symm
    apply Tuple.eq_sort_iff.mpr
    constructor <;> decide

private theorem binary_convolution :
    integralConvolutionElement ℤ 2 2 =
      MonoidAlgebra.single 1 3 + MonoidAlgebra.single (Equiv.swap (0 : Fin 2) 1) (-1) := by
  classical
  calc
    integralConvolutionElement ℤ 2 2 =
        ∑ z : Fin 2 × Fin 2,
          MonoidAlgebra.single (Tuple.sort ![z.1, z.2])
            ((Tuple.sort ![z.1, z.2]).sign : ℤ) := by
      exact ((finTwoArrowEquiv (Fin 2)).symm.sum_comp
        (fun f : Fin 2 → Fin 2 =>
          MonoidAlgebra.single (Tuple.sort f) ((Tuple.sort f).sign : ℤ))).symm
    _ = _ := by
      ext σ
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, binary_sort, Finsupp.single_apply]
      <;> ring

example : (integralConvolutionElement ℤ 2 2).coeff 1 = 3 ∧
    (integralConvolutionElement ℤ 2 2).coeff (Equiv.swap (0 : Fin 2) 1) = -1 := by
  rw [binary_convolution]
  constructor <;> norm_num [Finsupp.single_apply]

example : (trueLambdaElement ℤ 2 2 (by decide)).coeff 1 = -3 ∧
    (trueLambdaElement ℤ 2 2 (by decide)).coeff (Equiv.swap (0 : Fin 2) 1) = 1 := by
  rw [trueLambdaElement, binary_convolution]
  constructor <;> norm_num [MonoidAlgebra.coeff_smul_apply, Finsupp.single_apply]

example : (integralConvolutionElement ℤ 2 2 * integralConvolutionElement ℤ 2 2).coeff
    (Equiv.swap (0 : Fin 2) 1) = -6 := by
  rw [binary_convolution]
  norm_num [mul_add, add_mul, MonoidAlgebra.single_mul_single, Finsupp.single_apply]

example : trueLambdaElement ℤ 2 2 (by decide) * trueLambdaElement ℤ 2 2 (by decide) =
    -trueLambdaElement ℤ 2 4 (by decide) := by
  simpa using trueLambdaElement_mul ℤ 2 2 2 (by decide) (by decide)

example (m : ℕ) : integralConvolutionElement ℤ 0 m = 1 := by
  exact integralConvolutionElement_degree_zero ℤ m

example : integralConvolutionElement ℤ 3 0 = 0 := by
  exact integralConvolutionElement_zero_parameter ℤ 3 (by decide)

end BinaryConvolutionTests
