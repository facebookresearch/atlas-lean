/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PrimeDistribution
import Mathlib.Basic.Complex.Basic

open MathlibExt.NumberTheory.PrimeDistribution

example : discrepancy (Finsupp.single 1 (4 : ℝ)) (3 : ℕ+) 1 = 2 := by
  have ht : Nat.totient 3 = 2 := by decide
  norm_num [discrepancy, ht]

example : discrepancy (Finsupp.single 1 (4 : ℝ)) (3 : ℕ+) 2 = -2 := by
  have ht : Nat.totient 3 = 2 := by decide
  norm_num [discrepancy, ht]

example : discrepancy (Finsupp.single 0 (7 : ℝ)) (2 : ℕ+) 0 = 0 := by simp

example : convolution (Finsupp.single 2 (2 : ℝ)) (Finsupp.single 3 3) 6 = 6 := by
  norm_num [convolution_apply]

example : convolution (Finsupp.single 2 (2 : ℝ)) (Finsupp.single 3 3) 5 = 0 := by
  norm_num [convolution_apply]

example : convolution (Finsupp.single 0 (7 : ℝ)) (Finsupp.single 3 3) 0 = 0 := by simp

example : discrepancy (Finsupp.single 1 (4 : ℂ)) (3 : ℕ+) 1 = 2 := by
  have ht : Nat.totient 3 = 2 := by decide
  norm_num [discrepancy, ht]

example : convolution (Finsupp.single 2 (-2 : ℝ)) (Finsupp.single 3 3) 6 = -6 := by
  rw [convolution_apply, Finsupp.filter_single_of_pos (fun n : ℕ ↦ 0 < n) (by decide : 0 < 2),
    Finsupp.filter_single_of_pos (fun n : ℕ ↦ 0 < n) (by decide : 0 < 3)]
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  norm_num

example (β : ℕ →₀ ℂ) : convolution (Finsupp.single 0 (7 : ℂ)) β = 0 := by simp

example (α : ℕ →₀ ℝ) : convolution α (Finsupp.single 0 (-7 : ℝ)) = 0 :=
  convolution_single_zero_right α (-7)

example : ∃ a : (ZMod 3)ˣ,
    primitiveDiscrepancy (Finsupp.single 1 (4 : ℝ)) 3 =
      |discrepancy (Finsupp.single 1 (4 : ℝ)) (3 : ℕ+) a.val.val| :=
  primitiveDiscrepancy_attained _ 3

example (α : ℕ →₀ ℝ) : averagedDiscrepancy α 0 = 0 := by simp

example : dyadicVonMangoldt 2 0 = 0 := by
  simp [dyadicVonMangoldt]

example : dyadicVonMangoldt 2 2 = ArithmeticFunction.vonMangoldt 2 := by
  rw [dyadicVonMangoldt_apply 2 (by norm_num)]
  norm_num

example : dyadicVonMangoldt 2 4 = ArithmeticFunction.vonMangoldt 4 := by
  rw [dyadicVonMangoldt_apply 2 (by norm_num)]
  norm_num

example : dyadicVonMangoldt (5 / 2) 2 = 0 := by
  rw [dyadicVonMangoldt_apply _ (by norm_num)]
  norm_num

example : dyadicVonMangoldt (5 / 2) 3 = ArithmeticFunction.vonMangoldt 3 := by
  rw [dyadicVonMangoldt_apply _ (by norm_num)]
  norm_num

example : dyadicVonMangoldt (5 / 2) 5 = ArithmeticFunction.vonMangoldt 5 := by
  rw [dyadicVonMangoldt_apply _ (by norm_num)]
  norm_num

example : dyadicVonMangoldt (5 / 2) 6 = 0 := by
  rw [dyadicVonMangoldt_apply _ (by norm_num)]
  norm_num

example (n : ℕ) : dyadicVonMangoldt 0 n = 0 := by
  simp [dyadicVonMangoldt]

example (n : ℕ) : dyadicVonMangoldt (-1) n = 0 := by
  norm_num [dyadicVonMangoldt]
