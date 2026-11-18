/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.Probability.KrigingVariance

/-!
# Kriging certificate checks

Focused checks for `MathlibExt.Probability.KrigingVariance`: a
two-point identity example with identity covariance, and a
singular all-ones covariance where two different unit-sum
weights give equal variance (uniqueness needs definiteness).

These are elaboration and non-vacuity checks, not new results.
-/

open Matrix

/-- Two-point identity-covariance variance gap is `1 / 2`. -/
example : krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun i => if i = 0 then 1 else 0)
      - krigingErrorVariance (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (fun _ => 7 / 2) (fun _ => 1 / 2)
    = ((fun i => if i = 0 then (1 : ℝ) else 0) - fun _ => 1 / 2)
      ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ)
        *ᵥ ((fun i => if i = 0 then (1 : ℝ) else 0) - fun _ => 1 / 2)) :=
  kriging_variance_difference (lam := 3) (by simp [Matrix.IsSymm])
    (by
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, Fin.sum_univ_two] <;> norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
    (by simp [Fin.sum_univ_two]; norm_num)
