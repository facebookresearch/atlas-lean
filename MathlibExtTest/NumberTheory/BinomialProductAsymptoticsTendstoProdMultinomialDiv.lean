/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomialProductAsymptoticsTendstoProdMultinomialDiv
import MathlibExt.NumberTheory.CentralBinomialProductAsymptotics

/-!
# Tests for multinomial-product asymptotics

These tests specialize the theorem to two equal parts and compare the resulting constants.
-/

namespace MathlibExtTest.NumberTheory.BinomialProductAsymptoticsTendstoProdMultinomialDiv

open Filter Topology MetaMathlibExt

example : factorialProductConstant 2 / factorialProductConstant 1 ^ 2 ∈ Set.Ioo 0 1 := by
  simpa [Fin.sum_univ_two, Fin.prod_univ_two, pow_two] using
    (tendsto_prod_multinomial_div 2 (by decide) (fun _ => 1) (fun _ => by decide)).2

example : factorialProductConstant 2 < factorialProductConstant 1 ^ 2 := by
  have h : factorialProductConstant 2 / factorialProductConstant 1 ^ 2 < 1 := by
    simpa [Fin.sum_univ_two, Fin.prod_univ_two, pow_two] using
      (tendsto_prod_multinomial_div 2 (by decide) (fun _ => 1) (fun _ => by decide)).2.2
  exact (div_lt_one (pow_pos (factorialProductConstant_pos 1) 2)).mp h

example :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (n.centralBinom : ℝ)) /
        (factorialProductComparison 2 m / factorialProductComparison 1 m ^ 2))
      atTop (𝓝 (factorialProductConstant 2 / factorialProductConstant 1 ^ 2 *
        (2 * Real.pi) ^ (-(1 : ℝ) / 4))) := by
  have hn (n : ℕ) : Nat.multinomial Finset.univ (fun _ : Fin 2 => n) = n.centralBinom := by
    simpa only [Nat.multinomial, Fin.sum_univ_two, Fin.prod_univ_two,
      Nat.centralBinom_eq_two_mul_choose, two_mul, Nat.add_sub_cancel_left] using
      (Nat.choose_eq_factorial_div_factorial (Nat.le_add_right n n)).symm
  convert (tendsto_prod_multinomial_div 2 (by decide)
    (fun _ => 1) (fun _ => by decide)).1 using 1 <;>
    norm_num [Fin.sum_univ_two, Fin.prod_univ_two, hn, pow_two]

end MathlibExtTest.NumberTheory.BinomialProductAsymptoticsTendstoProdMultinomialDiv
