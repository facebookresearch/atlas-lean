/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_29.lean` (openbmb/ma-proofbench, commit 31bab4c):
the statement and its informal description, by L. Pu et al., licensed under the MIT License.

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

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Hilbert's integral operator on the positive half-line

`eLpNorm_hilbertIntegralOperator_le` bounds the operator with kernel `1 / (x + y)` on
real-valued functions in $L^p$ for $1 < p$.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBoundWanted

private noncomputable def weight (p t : ℝ) : ℝ := 1 / (t ^ (1 / p) * (1 + t))

private lemma integrableOn_weight {p : ℝ} (hp : 1 < p) :
    IntegrableOn (weight p) (Ioi 0) := by
  have hp' : 0 < p := zero_lt_one.trans hp
  have he : 1 - 1 / p ∈ Ioo (0 : ℝ) 1 :=
    ⟨sub_pos.mpr ((div_lt_one hp').mpr hp), sub_lt_self _ (by positivity)⟩
  apply (Real.integrableOn_rpowIntegrand₀₁_Ioi he zero_le_one).congr_fun _ measurableSet_Ioi
  intro t (ht : 0 < t)
  dsimp only
  rw [Real.rpowIntegrand₀₁_eq_pow_div he ht.le zero_le_one, sub_right_comm, sub_self,
    zero_sub, Real.rpow_neg ht.le]
  simp [weight, div_eq_mul_inv, mul_comm, add_comm]

private lemma integral_dilate {x : ℝ} (hx : 0 < x) (f : ℝ → ℝ) :
    (∫ y in Ioi 0, f y / (x + y)) = ∫ t in Ioi 0, f (t * x) / (1 + t) := by
  have h := integral_comp_mul_right_Ioi' (fun y ↦ f y / (x + y)) 0 hx
  rw [zero_mul, smul_eq_mul, ← integral_const_mul] at h
  refine h.symm.trans (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_)
  rw [show x + t * x = (1 + t) * x by ring]
  field_simp

private lemma lintegral_dilate {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (f : ℝ → ℝ) :
    (∫⁻ x in Ioi 0, (ENNReal.ofReal t ^ (1 / p) * ‖f (t * x)‖ₑ) ^ p) =
      ∫⁻ y in Ioi 0, ‖f y‖ₑ ^ p := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (f := (t * ·)) (f' := fun _ ↦ t)
    (s := Ioi 0) measurableSet_Ioi
    (fun x _ ↦ by simpa using (hasDerivAt_id x).const_mul t |>.hasDerivWithinAt)
    (mul_right_injective₀ ht.ne').injOn (fun y ↦ ‖f y‖ₑ ^ p)
  simpa [ENNReal.mul_rpow_of_nonneg _ _ hp.le, one_div, hp.ne', image_mul_left_Ioi ht,
    abs_of_pos ht] using h.symm

-- Hölder against the constant function on the measure with density given by the kernel.
private lemma holder_moment {p : ℝ} (hp : 1 < p) (ν : Measure ℝ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t, g t ∂ν) ^ p ≤ ν univ ^ (p - 1) * ∫⁻ t, g t ^ p ∂ν := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg.aemeasurable
    (g := fun _ ↦ 1) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at h
  have h' := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, one_div, ENNReal.rpow_inv_rpow hpq.pos.ne',
    ← ENNReal.rpow_mul, one_div_mul_eq_div, hpq.div_conj_eq_sub_one, mul_comm] at h'
  exact h'

private lemma weighted_bound {p : ℝ} (hp : 1 < p) {f : ℝ → ℝ} (hf : Measurable f) :
    let μ := volume.restrict (Ioi (0 : ℝ))
    let ν := μ.withDensity (fun t ↦ ENNReal.ofReal (weight p t))
    (∫⁻ x, ‖∫ y in Ioi 0, f y / (x + y)‖ₑ ^ p ∂μ) ≤
      ν univ ^ p * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  intro μ ν
  -- The factor t^(1/p) compensates for dilation in the Lᵖ norm.
  let G (x t : ℝ) := ENNReal.ofReal t ^ (1 / p) * ‖f (t * x)‖ₑ
  have hG : Measurable (Function.uncurry G) := by unfold G Function.uncurry; fun_prop
  have hGt (x : ℝ) : Measurable (G x) := hG.of_uncurry_left
  have hν : ∀ᵐ t ∂ν, 0 < t :=
    (withDensity_absolutelyContinuous μ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hpoint (x : ℝ) (hx : 0 < x) :
      ‖∫ y in Ioi 0, f y / (x + y)‖ₑ ≤ ∫⁻ t, G x t ∂ν := by
    rw [integral_dilate hx, lintegral_withDensity_eq_lintegral_mul μ
      (by unfold weight; fun_prop) (hGt x)]
    refine (eNorm_integral_le_lintegral_eNorm _).trans_eq (lintegral_congr_ae ?_)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    have ht' : 0 < t := ht
    have hpow := Real.rpow_pos_of_pos ht' (1 / p)
    rw [show f (t * x) / (1 + t) = (weight p t * t ^ (1 / p)) * f (t * x) by
      unfold weight; field_simp]
    rw [eNorm_mul, eNorm_mul, Real.eNorm_of_nonneg (by unfold weight; positivity),
      Real.eNorm_of_nonneg hpow.le, ← ENNReal.ofReal_rpow_of_pos ht', mul_assoc]
    rfl
  calc
    _ ≤ ∫⁻ x, ν univ ^ (p - 1) * ∫⁻ t, G x t ^ p ∂ν ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
      exact (ENNReal.rpow_le_rpow (hpoint x hx) (by linarith)).trans (holder_moment hp ν (hGt x))
    _ = ν univ ^ (p - 1) * ∫⁻ t, ∫⁻ x, G x t ^ p ∂μ ∂ν := by
      have hm := hG.pow_const p
      rw [lintegral_const_mul _ hm.lintegral_prod_right, lintegral_lintegral_swap hm.aemeasurable]
    _ = ν univ ^ (p - 1) * ((∫⁻ y, ‖f y‖ₑ ^ p ∂μ) * ν univ) := by
      congr 1
      rw [← lintegral_const]
      apply lintegral_congr_ae
      filter_upwards [hν] with t ht
      exact lintegral_dilate (by linarith) ht f
    _ = _ := by
      have hpow := ENNReal.rpow_add_of_nonneg (x := ν univ) (p - 1) 1 (by linarith) zero_le_one
      rw [sub_add_cancel, ENNReal.rpow_one] at hpow
      rw [hpow]
      ac_rfl

set_option linter.unusedVariables false in
/-- **An $L^p$ bound for Hilbert's integral operator.** Let $p$ be a real number with
$p > 1$ and let $T$ be the operator on functions $g : \mathbb{R} \to \mathbb{R}$ given by
$$Tg(x) = \int_0^\infty \frac{g(y)}{x+y}\,dy \qquad (x \in \mathbb{R}).$$
Let $f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0,\infty)$, compactly supported and zero
outside $[0,\infty)$, and put
$$C_p = \int_0^\infty \frac{dx}{x^{1/p}(1+x)}.$$
Then
$$\|Tf\|_{L^p([0,\infty))} \le C_p \, \|f\|_{L^p([0,\infty))},$$
where both norms are taken in $[0,\infty]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Integral,
integro-differential, and pseudodifferential operators),
`benchmark/level2/ma_proofbench_l2_29.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem eLpNorm_hilbertIntegralOperator_le
    (p : ℝ) (hp : 1 < p) (T : (ℝ → ℝ) → (ℝ → ℝ))
  (hT : ∀ g : ℝ → ℝ, ∀ x : ℝ, T g x = ∫ y in Set.Ici (0 : ℝ), g y / (x + y))
  (f : ℝ → ℝ) (hf_cont : ContinuousOn f (Set.Ici (0 : ℝ)))
  (hf_cpt : HasCompactSupport f)
  (hf_support : Function.support f ⊆ Set.Ici (0 : ℝ))
  (Cp : ℝ) (hCp : Cp = ∫ x in Set.Ici (0 : ℝ), 1 / (x ^ (1 / p) * (1 + x))) :
  eLpNorm (T f) (ENNReal.ofReal p) (volume.restrict (Set.Ici (0 : ℝ))) ≤
    ENNReal.ofReal Cp * eLpNorm f (ENNReal.ofReal p) (volume.restrict (Set.Ici (0 : ℝ))) := by
  classical
  have hp' : 0 < p := zero_lt_one.trans hp
  have hf : Measurable f := by
    rw [← indicator_eq_self.mpr hf_support]
    exact hf_cont.measurable_piecewise continuousOn_const measurableSet_Ici
  have hkernel : Measurable (fun z : ℝ × ℝ ↦ f z.2 / (z.1 + z.2)) := by fun_prop
  let μ := volume.restrict (Ioi (0 : ℝ))
  let ν := μ.withDensity (fun t ↦ ENNReal.ofReal (weight p t))
  have hTf : T f = fun x ↦ ∫ y in Ioi 0, f y / (x + y) := by
    funext x
    rw [hT, integral_Ici_eq_integral_Ioi]
  have hmass : ENNReal.ofReal Cp = ν univ := by
    rw [hCp, integral_Ici_eq_integral_Ioi, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    apply ofReal_integral_eq_lintegral_ofReal (integrableOn_weight hp)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    have : 0 < t := ht
    dsimp [weight]
    positivity
  rw [hTf, ← restrict_Ioi_eq_restrict_Ici, eLpNorm_eq_lintegral_rpow_eNorm_toReal
    (ENNReal.ofReal_pos.mpr hp').ne' ENNReal.ofReal_ne_top
    hkernel.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.ofReal_pos.mpr hp').ne'
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp'.le, hmass]
  have h := ENNReal.rpow_le_rpow (weighted_bound hp hf) (by positivity : 0 ≤ 1 / p)
  simpa only [one_div, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp'.le),
    ENNReal.rpow_rpow_inv hp'.ne'] using h

end MathlibExt.Analysis.OperatorTheory.HilbertIntegralOperatorLpBoundWanted
