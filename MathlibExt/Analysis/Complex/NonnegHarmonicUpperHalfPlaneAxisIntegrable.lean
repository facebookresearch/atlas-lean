/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_20.lean` (openbmb/ma-proofbench, commit 31bab4c):
the statement of `eq_zero_of_harmonicOnNhd_upperHalfPlane_of_nonneg_of_integrableOn_imagAxis`.
Authors: L. Pu et al. (MA-ProofBench)
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

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Axis integrability of nonnegative harmonic functions

A nonnegative harmonic function on the upper half-plane vanishes if its restriction to the
positive imaginary axis is integrable.
-/

namespace MathlibExt.Analysis.Complex.NonnegHarmonicUpperHalfPlaneAxisIntegrableWanted

open _root_.Complex InnerProductSpace MeasureTheory Metric Set

-- The Poisson kernel is bounded above by (R + d) / (R - d), where d is the distance
-- from the evaluation point to the center of the disk.
private theorem poissonKernel_le {c z x : ℂ} {R : ℝ}
    (hz : ‖z - c‖ < R) (hx : x ∈ sphere c R) :
    poissonKernel c z x ≤ (R + ‖z - c‖) / (R - ‖z - c‖) := by
  have hxnorm : ‖x - c‖ = R := mem_sphere_iff_norm.mp hx
  have hR : 0 < R := (norm_nonneg _).trans_lt hz
  have hgap : 0 < R - ‖z - c‖ := sub_pos.mpr hz
  have hdist : R - ‖z - c‖ ≤ ‖x - z‖ := by
    rw [sub_le_iff_le_add, ← hxnorm]
    exact norm_sub_le_norm_sub_add_norm_sub x z c
  rw [poissonKernel_def, hxnorm, sub_sub_sub_cancel_right, sq_sub_sq]
  calc
    _ ≤ (R + ‖z - c‖) * (R - ‖z - c‖) / (R - ‖z - c‖) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg (add_nonneg hR.le (norm_nonneg _)) hgap.le)
        (pow_pos hgap 2)
        (pow_le_pow_left₀ hgap.le hdist 2)
    _ = _ := by
      rw [sq, mul_div_mul_right _ _ hgap.ne']

private theorem le_mul_center {f : ℂ → ℝ} {c z : ℂ} {R : ℝ}
    (hf : HarmonicOnNhd f (closedBall c R)) (hnonneg : ∀ x ∈ sphere c R, 0 ≤ f x)
    (hz : ‖z - c‖ < R) :
    f z ≤ ((R + ‖z - c‖) / (R - ‖z - c‖)) * f c := by
  have hR : 0 < R := (norm_nonneg _).trans_lt hz
  have hfcont := hf.continuousOn.mono (sphere_subset_closedBall : sphere c R ⊆ closedBall c R)
  have hkcont : ContinuousOn (poissonKernel c z) (sphere c R) := by
    have hkernel : poissonKernel c z =
        fun x ↦ (‖x - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖x - z‖ ^ 2 := by
      ext x
      rw [poissonKernel_def, sub_sub_sub_cancel_right]
    rw [hkernel]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hne : x ≠ z := by
      rintro rfl
      exact hz.ne (mem_sphere_iff_norm.mp hx)
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  have hmean : Real.circleAverage f c R = f c :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by rwa [abs_of_pos hR])
  rw [← hf.circleAverage_poissonKernel_smul (mem_ball_iff_norm.mpr hz), ← hmean,
    ← smul_eq_mul, ← Real.circleAverage_smul]
  refine Real.circleAverage_mono
    ((hkcont.smul hfcont).circleIntegrable hR.le)
    ((continuousOn_const.smul hfcont).circleIntegrable hR.le) ?_
  rw [abs_of_pos hR]
  intro x hx
  exact mul_le_mul_of_nonneg_right (poissonKernel_le hz hx) (hnonneg x hx)

/-- **Nonnegative harmonic functions on the upper half-plane integrable along the imaginary axis
vanish.** Let $\mathbb{C}_{+}=\{z\in\mathbb{C}:\Im z>0\}$ be the upper half-plane. Suppose
$f:\mathbb{C}_{+}\to\mathbb{R}$ is harmonic and non-negative, and satisfies
\[
\int_{0}^{\infty}\lvert f(iy)\rvert\,dy<\infty.
\]
Then $f(z)=0$ for every $z\in\mathbb{C}_{+}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level2/ma_proofbench_l2_20.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem eq_zero_of_harmonicOnNhd_upperHalfPlane_of_nonneg_of_integrableOn_imagAxis
  (f : ℂ → ℝ)
  (hharm : InnerProductSpace.HarmonicOnNhd f UpperHalfPlane.upperHalfPlaneSet)
  (hnonneg : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ f z)
  (hint :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => |f (Complex.I * (y : ℂ))|)
      (Set.Ioi (0 : ℝ))) :
  ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z = 0 := by
  intro z hz
  by_contra! hzero
  have hfz : 0 < f z := lt_of_le_of_ne (hnonneg z hz) hzero.symm
  have hzIm : 0 < z.im := hz
  let a := ‖z‖ ^ 2 / z.im + z.im
  have ha : 0 ≤ a := by positivity
  have htail := hint.mono_set (Ioi_subset_Ioi ha)
  have hcoef : 0 < z.im * f z / 8 := by positivity
  refine not_integrableOn_Ioi_inv (a := a)
    ((htail.const_mul (z.im * f z / 8)⁻¹).mono' measurable_id.inv.aestronglyMeasurable ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : a < y)
  have hyIm : z.im < y := lt_of_le_of_lt (le_add_of_nonneg_left (by positivity)) hy
  have hy₀ : 0 < y := hzIm.trans hyIm
  let c : ℂ := I * (y : ℂ)
  let R : ℝ := y - z.im / 4
  have hcIm : c.im = y := by simp [c, mul_im]
  have hcRe : c.re = 0 := by simp [c, mul_re]
  have hnormSq : ‖z - c‖ ^ 2 = ‖z‖ ^ 2 + y ^ 2 - 2 * y * z.im := by
    simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, hcRe, hcIm, sub_zero]
    ring
  have hyNorm : ‖z‖ ^ 2 < y * z.im :=
    (div_lt_iff₀ hzIm).mp (lt_of_le_of_lt (le_add_of_nonneg_right hzIm.le) hy)
  -- The closed disk stays above the real axis and contains z with a fixed margin.
  have hdist : ‖z - c‖ ≤ y - z.im / 2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by linarith : 0 ≤ y - z.im / 2)).mp
    rw [hnormSq]
    nlinarith [sq_nonneg z.im]
  have hgap : z.im / 4 ≤ R - ‖z - c‖ := by dsimp [R]; linarith
  have hzr : ‖z - c‖ < R := by linarith
  have hsub : closedBall c R ⊆ UpperHalfPlane.upperHalfPlaneSet := by
    intro x hx
    have hxIm := (neg_le_abs (x - c).im).trans
      ((abs_im_le_norm _).trans (mem_closedBall_iff_norm.mp hx))
    rw [sub_im, hcIm] at hxIm
    change 0 < x.im
    dsimp [R] at hxIm
    linarith
  have hratio : (R + ‖z - c‖) / (R - ‖z - c‖) ≤ 2 * y / (z.im / 4) := by
    have hsum : R + ‖z - c‖ ≤ 2 * y := by dsimp [R]; linarith
    exact (div_le_div_of_nonneg_right hsum (sub_nonneg.mpr hzr.le)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hgap)
  have hfc : 0 ≤ f c := hnonneg c (by change 0 < c.im; rwa [hcIm])
  have hbound := (le_mul_center (hharm.mono hsub)
    (fun x hx => hnonneg x (hsub (sphere_subset_closedBall hx))) hzr).trans
    (mul_le_mul_of_nonneg_right hratio hfc)
  have hweight : f z * (z.im / 4) ≤ 2 * y * f c := by
    apply (le_div_iff₀ (show 0 < z.im / 4 by positivity)).mp
    simpa only [div_mul_eq_mul_div] using hbound
  change ‖y⁻¹‖ ≤ (z.im * f z / 8)⁻¹ * |f c|
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy₀), ← div_eq_inv_mul, le_div_iff₀ hcoef,
    mul_comm, ← div_eq_mul_inv, div_le_iff₀ hy₀, abs_of_nonneg hfc]
  linarith only [hweight]

end MathlibExt.Analysis.Complex.NonnegHarmonicUpperHalfPlaneAxisIntegrableWanted
