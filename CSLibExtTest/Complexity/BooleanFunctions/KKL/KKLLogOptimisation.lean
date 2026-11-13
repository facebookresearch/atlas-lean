/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogOptimisation
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLLogSobolev

/-!
# Tests for the edge-isoperimetric and log-optimisation bounds

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.KKLLogOptimisation` at the `AND` function on
`{0, 1}^Bool` (mean `m = 1/4`, total influence `1`):

* `klo_edge_isoperimetric` is `2 · 1/4 · log 4 ≤ 1`, with a positive left side;
* `klo_master_le` at `ρ = 0` is `1/4 - 1/16 ≤ 1/4`;
* the hypothesis of `klo_DeltaUpgrade` holds for every `φ` (`klo_master_le`), and
  `klo_deltaUpgrade_zero`, `klo_logOptimisation` give `KKLHypercontractive (1/2) 0`;
* `klo_one_sub_pow_le` at a small input.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- Hart's edge-isoperimetric inequality (natural-log form) at `AND`. -/
example : 2 * (1 / 4) * Real.log 4 ≤ (1 : ℝ) := by
  have h := klo_edge_isoperimetric andFun (by rw [bnt_uexp_andInd]; norm_num)
  rw [bnt_uexp_andInd, sum_finset_bool, fourier_andInd_empty, fourier_andInd_true,
    fourier_andInd_false, fourier_andInd_univ] at h
  norm_num at h ⊢
  linarith

example : 0 < 2 * (1 / 4) * Real.log (4 : ℝ) := by
  have := Real.log_pos (show (1 : ℝ) < 4 by norm_num)
  positivity

/-- `klo_master_le` at `AND`, `ρ = 0`. -/
example : (1 / 4 : ℝ) - (1 / 4) ^ (2 / (1 + (0 : ℝ) ^ 2)) ≤ (1 - 0 ^ 2) * 1 / 4 := by
  have h := klo_master_le andFun 0 le_rfl zero_le_one
  rw [bnt_uexp_andInd, ← khc_totalInfl_eq_fourierWeight, totalInfl_andInd] at h
  exact h

/-- The hypothesis of `klo_DeltaUpgrade` holds for every Boolean function. -/
example (φ : ConfigSpace (Fin 3) → Bool) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)
        - (bnt_uexp (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / (1 + ρ ^ 2))
      ≤ (1 - ρ ^ 2) * (∑ S : Finset (Fin 3), 4 * (S.card : ℝ)
          * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) / 4 :=
  klo_master_le φ ρ h0 h1

example : KKLHypercontractive (1 / 2) 0 := klo_logOptimisation klo_deltaUpgrade_zero

/-- `klo_one_sub_pow_le` at `x = 1/2`, `k = 3`: `1 - 1/8 ≤ 1/2 · 3`. -/
example : 1 - (1 / 2 : ℝ) ^ 3 ≤ (1 - 1 / 2) * (3 : ℕ) :=
  klo_one_sub_pow_le _ (by norm_num) (by norm_num) 3

end StatMechTest.BooleanFunctions
