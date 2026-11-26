/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.GeneralizedCentralBinomialArcsinSeries

open Finset MetaMathlibExt

-- The lowest permitted index has no T term and no correction below degree one.
example {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' k : ℕ, (4 : ℝ) ^ (k + 1 + 1) * x ^ (k + 1 + 1) /
        (((k : ℝ) + 1) * Nat.centralBinom (k + 1 + 1)) =
      (-2 + 4 * x) * (Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x)) + 2 * x := by
  refine (tsum_four_pow_div_sub_mul_centralBinom (n := 1) le_rfl hx0 hx1).trans ?_
  rw [show Icc 1 1 = ({1} : Finset ℕ) by decide]
  norm_num [zuritaS, zuritaT, zuritaSCoeff, sum_range_succ, Nat.centralBinom, Nat.choose]
  ring

-- At n = 3 both reversed T coefficients contribute and the degree-three correction remains.
example :
    ∑' k : ℕ, (4 : ℝ) ^ (k + 3 + 1) * (1 / 2) ^ (k + 3 + 1) /
        (((k : ℝ) + 1) * Nat.centralBinom (k + 3 + 1)) =
      24 / 25 - 4 / 5 * Real.arcsin (Real.sqrt (1 / 2)) := by
  refine (tsum_four_pow_div_sub_mul_centralBinom (n := 3) (by decide)
    (x := 1 / 2) (by norm_num) (by norm_num)).trans ?_
  rw [show Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
  have hr : Real.sqrt ((1 / 2 : ℝ) / (1 - 1 / 2)) = 1 := by
    rw [show (1 / 2 : ℝ) / (1 - 1 / 2) = 1 by norm_num, Real.sqrt_one]
  rw [hr]
  norm_num [zuritaS, zuritaT, zuritaTCoeff, zuritaTCoeffRev, zuritaC, zuritaSCoeff,
    sum_range_succ, Nat.centralBinom, Nat.choose]
  ring
