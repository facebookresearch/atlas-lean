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

-- The Taylor coefficients of arcsin(√x)^2 and arcsin(√x)√(x(1−x)), respectively.
private def arcsinSqCoeff (k : ℕ) : ℚ :=
  4 ^ k / ((2 : ℚ) * k ^ 2 * Nat.centralBinom k)

private def arcsinFactorCoeff : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | k + 2 => -(4 : ℚ) ^ (k + 1) / (2 * (k + 1) * (2 * (k + 1) + 1) * Nat.centralBinom (k + 1))

private def lowCorrection (n k : ℕ) : ℚ :=
  zuritaTCoeff n (k - 1) / ((k : ℚ) - n) +
    1 / 2 * ∑ l ∈ range k, zuritaSCoeff n l * zuritaMCoeff (n - l) (k - l - 1) / ((k : ℚ) - n) +
    (1 - (4 : ℚ) ^ k / Nat.centralBinom k) / ((k : ℚ) - n) ^ 2

private def diagonalCorrection (n : ℕ) : ℚ :=
  -(2 : ℚ) ^ (2 * n + 1) / Nat.centralBinom n +
    ∑ l ∈ range (n - 1), zuritaSCoeff n l *
      ((4 : ℚ) ^ (n - l) / ((↑(n - l : ℕ) : ℚ) * Nat.centralBinom (n - l)) -
        1 / 2 * ∑ p ∈ Icc 1 (n - l - 1),
          (4 : ℚ) ^ p * zuritaMCoeff (n - l) (n - l - 1 - p) /
            ((p : ℚ) * (2 * p + 1) * Nat.centralBinom p))

private def closedCoeff (n k : ℕ) : ℚ :=
  (2 : ℚ) ^ (2 * n + 1) / Nat.centralBinom n *
      (if n ≤ k then arcsinSqCoeff (k - n) else 0) -
    (∑ l ∈ range n, zuritaSCoeff n l *
      ∑ j ∈ range (n - l), zuritaMCoeff (n - l) j *
        (if l + j ≤ k then arcsinFactorCoeff (k - (l + j)) else 0)) +
    (if k ∈ Icc 1 (n - 1) then lowCorrection n k else 0) +
    (if k = n then diagonalCorrection n else 0)

-- No terms below degree two for n = 1, where the lower correction is empty.
example : (List.range 4).map (closedCoeff 1) = [0, 0, 8 / 3, 4 / 5] := by decide +kernel

-- For n = 3 both lower corrections and the diagonal correction cancel, and the tail begins
-- with 4^4 / C(8,4) and 4^5 / (4 C(10,5)). These checks use no series identity theorem.
example : (List.range 6).map (closedCoeff 3) = [0, 0, 0, 0, 128 / 35, 64 / 63] := by decide +kernel

example : ((3 : ℚ) - 1 / 2) * zuritaMCoeff 3 0 = 1 ∧
    ((3 : ℚ) - 2 - 1 / 2) * zuritaMCoeff 3 2 = (3 - 2) * zuritaMCoeff 3 1 := by
  norm_num [zuritaMCoeff]

example : zuritaM 3 (1 / 2) = 14 / 15 := by
  rw [zuritaM_eq_sum_range]
  norm_num [sum_range_succ, zuritaMCoeff]

private theorem sqrt_half_mul_one_sub : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
  rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

-- Client at the smallest n and at a point strictly inside the real interval.
example :
    ∑' k : ℕ, (4 : ℝ) ^ (k + 1 + 1) * (1 / 2) ^ (k + 1 + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + 1 + 1)) =
      2 * Real.arcsin (Real.sqrt (1 / 2)) ^ 2 + 2 * Real.arcsin (Real.sqrt (1 / 2)) - 2 := by
  refine (tsum_four_pow_div_sub_sq_mul_centralBinom (n := 1) le_rfl
    (x := 1 / 2) (by norm_num) (by norm_num)).trans ?_
  rw [sqrt_half_mul_one_sub]
  norm_num [zuritaM_eq_sum_range, zuritaSCoeff, zuritaMCoeff, sum_range_succ,
    Nat.centralBinom, Nat.choose, show Icc 1 0 = (∅ : Finset ℕ) by decide]
  ring

-- At n = 2 the lower correction has one term, as does the inner sum in the degree-two correction.
example :
    ∑' k : ℕ, (4 : ℝ) ^ (k + 2 + 1) * (1 / 2) ^ (k + 2 + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + 2 + 1)) =
      4 / 3 * Real.arcsin (Real.sqrt (1 / 2)) ^ 2 +
        16 / 9 * Real.arcsin (Real.sqrt (1 / 2)) - 47 / 27 := by
  refine (tsum_four_pow_div_sub_sq_mul_centralBinom (n := 2) (by decide)
    (x := 1 / 2) (by norm_num) (by norm_num)).trans ?_
  rw [sqrt_half_mul_one_sub]
  norm_num [zuritaM_eq_sum_range, zuritaSCoeff, zuritaMCoeff, zuritaTCoeff, zuritaTCoeffRev,
    zuritaC, sum_range_succ, Nat.centralBinom, Nat.choose, show Icc 1 1 = ({1} : Finset ℕ) by decide]
  ring
