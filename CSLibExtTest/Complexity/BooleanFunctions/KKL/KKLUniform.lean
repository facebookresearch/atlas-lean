/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.BourgainPerCoord

/-!
# Tests for the KKL inequality on the uniform cube with constant 2

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.RhoOptimiseClose2`:

* `cro2_rhoOptimise : bph_RhoOptimise 2` at the `AND` function on `{0, 1}^Bool`: its hypothesis
  is supplied by `bph_capped_hc`, and the conclusion is the Fourier-side inequality
  `2 · 3/16 · log 2 ≤ 1`;
* the integral bounds `cro2_integral_rhs_le` (at `δ = 1/2`), `cro2_integral_one_sub_pow` and
  `cro2_integral_lhs` (at the constant weight on the subsets of `Bool`, value `12`).
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- `cro2_rhoOptimise` at `AND`. -/
example : 2 * (3 / 16) * Real.log 2 ≤ (1 : ℝ) := by
  have h := cro2_rhoOptimise andFun (fun ρ h0 h1 => bph_capped_hc h0 h1 andFun)
  rw [maxInfl_andInd, sum_erase_empty_finset_bool, ← khc_totalInfl_eq_fourierWeight,
    totalInfl_andInd, fourier_andInd_true, fourier_andInd_false, fourier_andInd_univ] at h
  norm_num at h ⊢
  linarith

example : (∫ u in (0 : ℝ)..1, (1 / 2 : ℝ) ^ (u / (2 - u))) ≤ 2 / (-(Real.log (1 / 2))) :=
  cro2_integral_rhs_le _ (by norm_num) (by norm_num)

example : ∫ u in (0 : ℝ)..1, (1 - u) ^ 3 = 1 / 4 := by
  rw [cro2_integral_one_sub_pow]; norm_num

example :
    (∫ u in (0 : ℝ)..1, ∑ S : Finset Bool, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * 1) = 12 := by
  rw [cro2_integral_lhs, sum_erase_empty_finset_bool]; norm_num

end StatMechTest.BooleanFunctions
