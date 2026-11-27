/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Monochromatic CT attenuation

## i. Overview

For monochromatic absorption-only transmission
`I = I0 * exp (-L)` with `I0 > 0`, the log attenuation recovers
the line integral `L`, in both sign conventions. An equal
two-energy mixture shows that replacing the log of a mixture
transmission by the mean attenuation is not exact.

## ii. Key results

* `attenuation_log_inversion`: `-log (I / I0) = L`.
* `attenuation_log_ratio`: `log (I0 / I) = L`.
* `mixture_log_ne_mean`: the two-energy mixture counterexample.

## iii. Table of contents

* A. Log attenuation inversion.
* B. Mixture counterexample.

## iv. References

* The Beer-Lambert law for monochromatic X-ray attenuation and
  its CT line-integral form, as in Kak and Slaney, *Principles of
  Computerized Tomographic Imaging* (1988), Chapter 1.
-/

@[expose] public section

namespace PhyslibExt.BiomedicalImaging.CTAttenuation

/-! ## A. Log attenuation inversion. -/

/-- **Monochromatic attenuation inversion.** For incident
intensity `I0 > 0` and line integral `L`, the transmitted
intensity `I = I0 * Real.exp (-L)` satisfies
`-Real.log (I / I0) = L`. -/
lemma attenuation_log_inversion {I0 L : ℝ} (hI0 : 0 < I0) :
    -Real.log ((I0 * Real.exp (-L)) / I0) = L := by
  have hI0' : I0 ≠ 0 := ne_of_gt hI0
  have h : (I0 * Real.exp (-L)) / I0 = Real.exp (-L) := by field_simp
  rw [h, Real.log_exp, neg_neg]

/-- **Attenuation as log ratio.** With the same hypotheses,
`Real.log (I0 / I) = L` for `I = I0 * Real.exp (-L)`. -/
lemma attenuation_log_ratio {I0 L : ℝ} (hI0 : 0 < I0) :
    Real.log (I0 / (I0 * Real.exp (-L))) = L := by
  have hI0' : I0 ≠ 0 := ne_of_gt hI0
  have hexp : Real.exp (-L) ≠ 0 := (Real.exp_pos _).ne'
  have h : I0 / (I0 * Real.exp (-L)) = (Real.exp (-L))⁻¹ := by field_simp
  rw [h, Real.log_inv, Real.log_exp, neg_neg]

/-! ## B. Mixture counterexample. -/

/-- **Two-energy mixture counterexample.** Replacing the log of
an equal two-energy mixture transmission by the mean attenuation
is not exact: for attenuations `0` and `2`,
`-log ((exp 0 + exp (-2)) / 2) ≠ 1`. -/
lemma mixture_log_ne_mean :
    -Real.log ((Real.exp (0:ℝ) + Real.exp (-2)) / 2) ≠ 1 := by
  intro hcon
  have hXpos : 0 < (Real.exp (0:ℝ) + Real.exp (-2)) / 2 := by positivity
  have hlog : Real.log ((Real.exp (0:ℝ) + Real.exp (-2)) / 2) = -1 := by linarith
  have hXeq : (Real.exp (0:ℝ) + Real.exp (-2)) / 2 = Real.exp (-1) := by
    have hexp := Real.exp_log hXpos
    rw [hlog] at hexp
    exact hexp.symm
  rw [Real.exp_zero] at hXeq
  have hadd : (-2:ℝ) = (-1) + (-1) := by ring
  rw [hadd, Real.exp_add] at hXeq
  have htpos : 0 < Real.exp (-1:ℝ) := Real.exp_pos _
  have htlt : Real.exp (-1:ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  nlinarith [hXeq, htlt, htpos]


end PhyslibExt.BiomedicalImaging.CTAttenuation
