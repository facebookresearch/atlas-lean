/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_35.lean` (openbmb/ma-proofbench, commit 31bab4c):
the statement of `integral_sin_div_sq_Ioi_eq_pi_div_two`, from MA-ProofBench by L. Pu et al.
The adapted statement is distributed under the MIT License:

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import MathlibExt.Analysis.SineIntegral

/-!
# Integral of the squared sinc function over the half-line

The integral of `(sin x / x) ^ 2` over the positive half-line is `π / 2`.
We differentiate `Si (2 * x) - sin x ^ 2 / x` and use the Dirichlet integral at infinity.
-/

namespace MathlibExt.Analysis.SpecialFunctions.IntegralSincSqHalfLineWanted

open Filter MeasureTheory Real Set SineIntegral
open scoped Topology

private lemma hasDerivAt_primitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => sineIntegral (2 * t) - sin t ^ 2 / t) ((sin x / x) ^ 2) x := by
  have hSi : HasDerivAt sineIntegral (sinc (2 * x)) (2 * x) :=
    intervalIntegral.integral_hasDerivAt_right (continuous_sinc.intervalIntegrable 0 _)
      continuous_sinc.aestronglyMeasurable.stronglyMeasurableAtFilter continuous_sinc.continuousAt
  have h := (hSi.comp x ((hasDerivAt_id x).const_mul 2)).sub
    (((hasDerivAt_sin x).pow 2).div (hasDerivAt_id x) hx.ne')
  apply h.congr_deriv
  rw [sinc_of_ne_zero (by positivity : 2 * x ≠ 0), sin_two_mul]
  dsimp
  field_simp
  ring

/-- **Integral of the squared sinc function over the half-line.** The integral of
$(\sin x / x)^2$ over $(0, \infty)$ is $\pi/2$:

$$\int_0^\infty \left(\frac{\sin x}{x}\right)^2 dx = \frac{\pi}{2}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_35.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem integral_sin_div_sq_Ioi_eq_pi_div_two :
    ∫ x in Set.Ioi (0 : ℝ), (Real.sin x / x) ^ 2 = Real.pi / 2 := by
  have hcont : Continuous (fun x : ℝ => sin x ^ 2 / x) := by
    convert continuous_sin.mul continuous_sinc using 1
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · simp [sinc_of_ne_zero hx, sq, mul_div_assoc]
  have hlim : Tendsto (fun x : ℝ => sin x ^ 2 / x) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_id.const_div_atTop 1)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_le_div_of_nonneg_right (sin_sq_le_one x) hx.le
  have hSi := tendsto_sineIntegral_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : 0 < (2 : ℝ)))
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((continuous_sineIntegral.comp (continuous_const.mul continuous_id)).sub hcont
      |>.continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_primitive hx) (fun x _ => sq_nonneg _) (hSi.sub hlim)
  simpa [sineIntegral_zero] using h

end MathlibExt.Analysis.SpecialFunctions.IntegralSincSqHalfLineWanted
