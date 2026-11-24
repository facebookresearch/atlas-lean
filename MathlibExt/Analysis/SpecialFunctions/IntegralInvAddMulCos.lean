/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_89.lean` (openbmb/ma-proofbench, commit 31bab4c):
the statement of `integral_one_div_add_mul_cos_eq`, from MA-ProofBench by L. Pu et al.
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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-! # Integral of the reciprocal of a cosine plus a constant -/

namespace MathlibExt.Analysis.SpecialFunctions.IntegralInvAddMulCosWanted

open InnerProductSpace Real

/-- **Integral of $1/(a + b\cos\theta)$ over a period.** Let $a$ and $b$ be real numbers with
$a > |b|$. Then

$$\int_0^{2\pi} \frac{d\theta}{a + b\cos\theta} = \frac{2\pi}{\sqrt{a^2 - b^2}}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_89.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem integral_one_div_add_mul_cos_eq (a b : ℝ) (hab : a > |b|) :
    (∫ θ in 0..(2 * Real.pi), (1 / (a + b * Real.cos θ))) =
      (2 * Real.pi) / Real.sqrt (a ^ 2 - b ^ 2) := by
  let s := Real.sqrt (a ^ 2 - b ^ 2)
  have ha : 0 < a := (abs_nonneg b).trans_lt hab
  have hdiff : 0 < a ^ 2 - b ^ 2 := sub_pos.mpr (sq_lt_sq.mpr (by rwa [abs_of_pos ha]))
  have hs : 0 < s := Real.sqrt_pos.2 hdiff
  have hs_sq : s ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt hdiff.le
  -- On the circle of radius a + s, the Poisson kernel at -b is s / (a + b cos θ).
  let R := a + s
  have hR : 0 < R := add_pos ha hs
  have hmem : ((-b : ℝ) : ℂ) ∈ Metric.ball 0 R := by
    simpa [Metric.mem_ball, R] using hab.trans (lt_add_of_pos_right a hs)
  have hkernel (θ : ℝ) :
      poissonKernel 0 ((-b : ℝ) : ℂ) (circleMap 0 R θ) = s * (1 / (a + b * cos θ)) := by
    rw [poissonKernel_def, sub_zero, sub_zero, norm_circleMap_zero, abs_of_pos hR,
      Complex.sq_norm (_ - _), Complex.normSq_sub, Complex.normSq_eq_norm_sq (circleMap ..),
      norm_circleMap_zero, abs_of_pos hR, Complex.normSq_ofReal, Complex.conj_ofReal,
      Complex.re_mul_ofReal, circleMap_zero_re, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hnum : R ^ 2 - (-b) ^ 2 = (2 * R) * s := by
      dsimp [R]
      linarith only [hs_sq]
    have hden : R ^ 2 + -b * -b - 2 * (R * cos θ * -b) = (2 * R) * (a + b * cos θ) := by
      dsimp [R]
      linarith only [hs_sq]
    rw [hnum, hden, mul_div_mul_left _ _ (by positivity), mul_one_div]
  have hmean := (harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul hmem
  simp only [circleAverage_def, smul_eq_mul, Pi.mul_apply, mul_one, hkernel,
    intervalIntegral.integral_const_mul] at hmean
  apply (eq_div_iff hs.ne').2
  field_simp [Real.pi_ne_zero] at hmean
  simpa only [mul_comm s] using hmean

end MathlibExt.Analysis.SpecialFunctions.IntegralInvAddMulCosWanted
