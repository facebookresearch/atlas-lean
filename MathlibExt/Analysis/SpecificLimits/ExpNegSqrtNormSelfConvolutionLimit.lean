/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_90.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029).
Authors: L. Pu et al. (MA-ProofBench, arXiv:2606.13782).
The definition of `f` and the theorem statement are adapted from this MIT-licensed source.

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

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Self-convolution asymptotics of the exponential of the negative square root of the norm

On the Euclidean plane, the self-convolution of `f x = exp (-√‖x‖)` divided by `f` tends to
twice the integral of `f` as the norm of the evaluation point tends to infinity.
-/

@[expose] public section

open scoped Convolution

namespace MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimitWanted

/-- **The function $e^{-\sqrt{\|x\|}}$ on the plane.** Let $f : \mathbb{R}^2 \to \mathbb{R}$ be
$f(x) = e^{-\sqrt{\|x\|}}$, where $\|x\|$ is the Euclidean norm of $x$. -/
noncomputable def f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x =>
  Real.exp (-(Real.sqrt ‖x‖))

open Filter MeasureTheory

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem integrable_exp_neg_mul_sqrt_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Plane => Real.exp (-c * Real.sqrt ‖x‖)) := by
  apply (integrable_fun_norm_addHaar volume (f := fun r => Real.exp (-c * Real.sqrt r))).2
  simpa [Real.sqrt_eq_rpow, Real.rpow_one, smul_eq_mul, finrank_euclideanSpace] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1 / 2) (s := 1)
      (by norm_num) (by norm_num) hc)

private noncomputable def kernel (a x : Plane) : ℝ :=
  f x * f (a - x) / f a

private theorem kernel_eq_exp (a x : Plane) :
    kernel a x = Real.exp (-Real.sqrt ‖x‖ + (Real.sqrt ‖a‖ - Real.sqrt ‖a - x‖)) := by
  rw [kernel, f, f, f, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

-- On the half where x is closer to 0 than to a, the decay in x gives an integrable bound.
private theorem kernel_le (a x : Plane) (hx : ‖x‖ ≤ ‖a - x‖) :
    kernel a x ≤ Real.exp (-(1 / 2) * Real.sqrt ‖x‖) := by
  have htriangle : ‖a‖ ≤ ‖a - x‖ + ‖x‖ := by
    simpa using norm_add_le (a - x) x
  have hsqrt : Real.sqrt ‖a‖ ≤ Real.sqrt ‖a - x‖ + Real.sqrt ‖x‖ / 2 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hprod := mul_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hx)) (Real.sqrt_nonneg ‖x‖)
    nlinarith only [htriangle, hprod, Real.sq_sqrt (norm_nonneg x),
      Real.sq_sqrt (norm_nonneg (a - x)), sq_nonneg (Real.sqrt ‖x‖)]
  rw [kernel_eq_exp, Real.exp_le_exp]
  linarith

-- The two reflected weights sum to one, including on the perpendicular bisector.
private noncomputable def nearWeight (a x : Plane) : ℝ :=
  if ‖x‖ < ‖a - x‖ then 1 else if ‖a - x‖ < ‖x‖ then 0 else 1 / 2

private noncomputable def nearKernel (a x : Plane) : ℝ :=
  nearWeight a x * kernel a x

private theorem measurable_nearKernel (a : Plane) : Measurable (nearKernel a) := by
  apply Measurable.mul
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const
      (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
        measurable_const measurable_const)
  · unfold kernel f
    fun_prop

private theorem norm_nearKernel_le (a x : Plane) :
    ‖nearKernel a x‖ ≤ Real.exp (-(1 / 2) * Real.sqrt ‖x‖) := by
  by_cases h : ‖a - x‖ < ‖x‖
  · simpa [nearKernel, nearWeight, h, not_lt.mpr h.le] using
      (Real.exp_nonneg (-(1 / 2) * Real.sqrt ‖x‖))
  · have hk : 0 ≤ kernel a x := by rw [kernel_eq_exp]; positivity
    have hw₀ : 0 ≤ nearWeight a x := by
      unfold nearWeight
      split_ifs <;> norm_num
    have hw₁ : nearWeight a x ≤ 1 := by
      unfold nearWeight
      split_ifs <;> norm_num
    rw [nearKernel, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw₀ hk)]
    exact (mul_le_of_le_one_left hk hw₁).trans (kernel_le a x (le_of_not_gt h))

private noncomputable abbrev normAtTop : Filter Plane :=
  Filter.comap (fun a : Plane => ‖a‖) Filter.atTop

private theorem tendsto_sqrt_norm_sub (x : Plane) :
    Tendsto (fun a : Plane => Real.sqrt ‖a‖ - Real.sqrt ‖a - x‖) normAtTop (nhds 0) := by
  have hnorm : Tendsto (fun a : Plane => ‖a‖) normAtTop atTop := tendsto_comap
  have hsqrt : Tendsto (fun a : Plane => Real.sqrt ‖a‖) normAtTop atTop :=
    Real.tendsto_sqrt_atTop.comp hnorm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (.of_forall fun a => norm_nonneg _) ?_
    ((tendsto_const_nhds (x := ‖x‖)).div_atTop hsqrt)
  filter_upwards [hsqrt.eventually_ge_atTop 1] with a ha
  rw [Real.norm_eq_abs, le_div_iff₀ (zero_lt_one.trans_le ha)]
  calc
    _ ≤ |Real.sqrt ‖a‖ - Real.sqrt ‖a - x‖| * (Real.sqrt ‖a‖ + Real.sqrt ‖a - x‖) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (abs_nonneg _)
    _ = |‖a‖ - ‖a - x‖| := by
      rw [← abs_of_nonneg (show 0 ≤ Real.sqrt ‖a‖ + Real.sqrt ‖a - x‖ by positivity),
        ← abs_mul]
      congr 1
      nlinarith only [Real.sq_sqrt (norm_nonneg a), Real.sq_sqrt (norm_nonneg (a - x))]
    _ ≤ ‖x‖ := by simpa using abs_norm_sub_norm_le a (a - x)

private theorem tendsto_nearKernel (x : Plane) :
    Tendsto (fun a => nearKernel a x) normAtTop (nhds (f x)) := by
  have hnorm : Tendsto (fun a : Plane => ‖a‖) normAtTop atTop := tendsto_comap
  have heq : (fun a => kernel a x) =ᶠ[normAtTop] fun a => nearKernel a x := by
    filter_upwards [hnorm.eventually_gt_atTop (2 * ‖x‖)] with a ha
    have ht : ‖a‖ ≤ ‖a - x‖ + ‖x‖ := by simpa using norm_add_le (a - x) x
    have hx : ‖x‖ < ‖a - x‖ := by linarith
    simp [nearKernel, nearWeight, hx]
  apply Tendsto.congr' heq
  simpa only [kernel_eq_exp, f, add_zero] using
    ((tendsto_const_nhds (x := -Real.sqrt ‖x‖)).add (tendsto_sqrt_norm_sub x)).rexp

private theorem nearKernel_add_reflect (a x : Plane) :
    nearKernel a x + nearKernel a (a - x) = kernel a x := by
  have hk : kernel a (a - x) = kernel a x := by simp [kernel, mul_comm]
  rw [nearKernel, nearKernel, hk, ← add_mul]
  suffices nearWeight a x + nearWeight a (a - x) = 1 by rw [this, one_mul]
  simp only [nearWeight, sub_sub_cancel]
  rcases lt_trichotomy ‖x‖ ‖a - x‖ with h | h | h
  · simp [h, not_lt.mpr h.le]
  · norm_num [h]
  · simp [h, not_lt.mpr h.le]

private theorem convolution_div_eq (a : Plane) :
    (f ⋆ f) a / f a = 2 * ∫ x, nearKernel a x := by
  have hNear : Integrable (nearKernel a) :=
    (integrable_exp_neg_mul_sqrt_norm (by norm_num)).mono'
      (measurable_nearKernel a).aestronglyMeasurable (.of_forall (norm_nearKernel_le a))
  have hReflect : Integrable (fun x => nearKernel a (a - x)) := hNear.comp_sub_left a
  calc
    _ = ∫ x, kernel a x := by
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, kernel,
        integral_div]
    _ = ∫ x, (nearKernel a x + nearKernel a (a - x)) :=
      integral_congr_ae (.of_forall fun x => (nearKernel_add_reflect a x).symm)
    _ = _ := by rw [integral_add hNear hReflect, integral_sub_left_eq_self, two_mul]

/-- **Asymptotics of the self-convolution of $e^{-\sqrt{\|x\|}}$.** Let $f : \mathbb{R}^2 \to
\mathbb{R}$ be $f(x) = e^{-\sqrt{\|x\|}}$, where $\|x\|$ is the Euclidean norm, and let $f * f$ be
the convolution of $f$ with itself with respect to Lebesgue measure. Then

$$\lim_{\|a\| \to \infty} \frac{(f * f)(a)}{f(a)} = 2 \int_{\mathbb{R}^2} f(x)\,dx.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Measures,
integration, derivative, holomorphy), `benchmark/level2/ma_proofbench_l2_90.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem tendsto_convolution_self_div_atTop_norm :
    Filter.Tendsto
      (fun a : EuclideanSpace ℝ (Fin 2) => ((f ⋆ f) a) / f a)
      (Filter.comap (fun a : EuclideanSpace ℝ (Fin 2) => ‖a‖) Filter.atTop)
      (nhds (2 * ∫ x : EuclideanSpace ℝ (Fin 2), f x)) := by
  have hlim : Tendsto (fun a : Plane => ∫ x, nearKernel a x) normAtTop
      (nhds (∫ x, f x)) :=
    tendsto_integral_filter_of_dominated_convergence
      (fun x => Real.exp (-(1 / 2) * Real.sqrt ‖x‖))
      (.of_forall fun a => (measurable_nearKernel a).aestronglyMeasurable)
      (.of_forall fun a => .of_forall (norm_nearKernel_le a))
      (integrable_exp_neg_mul_sqrt_norm (by norm_num))
      (.of_forall tendsto_nearKernel)
  simpa only [convolution_div_eq] using hlim.const_mul 2

end MathlibExt.Analysis.SpecificLimits.ExpNegSqrtNormSelfConvolutionLimitWanted
