/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The Kong–Cox linear model's score at zero -/

namespace WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted

/-- **The score at `δ = 0`** (Kong and Cox 1997). Let `ι` be a finite set of independent
pedigrees with weights `γᵢ` and null posterior mean scores `Z̄ᵢ` (real numbers). The function
`δ ↦ ∑ᵢ log (1 + δ γᵢ Z̄ᵢ)` has derivative `∑ᵢ γᵢ Z̄ᵢ` at `δ = 0`.

Source: Kong and Cox (1997). -/
public theorem hasDerivAt_sum_log_zero {ι : Type*} [Fintype ι] (γ Zbar : ι → ℝ) :
    HasDerivAt (fun δ => ∑ i, Real.log (1 + δ * (γ i * Zbar i))) (∑ i, γ i * Zbar i) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have ha : HasDerivAt (fun δ : ℝ => 1 + δ * (γ i * Zbar i)) (γ i * Zbar i) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (γ i * Zbar i)).const_add 1)
  have hne : (1 : ℝ) + 0 * (γ i * Zbar i) ≠ 0 := by simp
  simpa only [zero_mul, add_zero, div_one] using ha.log hne

end WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted
