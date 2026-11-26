/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_84.lean` (OpenBMB MA-ProofBench):
Authors: L. Pu et al.
Licensed under the MIT License. The theorem statement and its original problem description
are adapted from openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029.

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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Hadamard

/-!
# Hausdorff–Young inequality for Schwartz functions

The Fourier transform on Euclidean space satisfies the Hausdorff–Young inequality
with constant one for complex-valued Schwartz functions and conjugate exponents.
-/

open MeasureTheory Set Filter Complex HadamardThreeLines
open scoped FourierTransform ENNReal RealInnerProductSpace ContDiff Topology ComplexConjugate

namespace MathlibExt.Analysis.Fourier.HausdorffYoungSchwartzWanted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

-- On integrable L² inputs the integral Fourier transform represents the L² Fourier transform.
private theorem fourier_ae_eq_L2 {f : E → ℂ} (h₁ : Integrable f volume) (h₂ : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure E)) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (continuous_inner (𝕜 := ℝ)) h₁
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num))
  intro g hg hgc
  let φ := (hgc.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have hflip : (innerₗ E).flip = innerₗ E := by
    ext x y
    exact real_inner_comm x y
  have hswap : ∫ x, 𝓕 f x * φ x = ∫ x, f x * (𝓕 φ) x := by
    have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (μ := (volume : Measure E)) (ν := (volume : Measure E)) (L := innerₗ E)
      (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
      (continuous_inner (𝕜 := ℝ)) h₁ φ.integrable
    rw [hflip] at h
    simp_rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simpa only [ContinuousLinearMap.mul_apply', VectorFourier.fourierIntegral,
      innerₗ_apply_apply] using h
  have hd := congrArg (fun d : TemperedDistribution E ℂ => d φ)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
    at hd
  calc
    (∫ x, g x • 𝓕 f x) = ∫ x, 𝓕 f x * φ x := by
      congr with x
      rw [Complex.real_smul, mul_comm]
      rfl
    _ = ∫ x, f x * 𝓕 φ x := hswap
    _ = ∫ x, 𝓕 φ x * h₂.toLp f x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx, mul_comm]
    _ = ∫ x, g x • (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure E)) x := by
      rw [hd]
      simp only [Complex.real_smul]
      rfl

private theorem norm_toLp_two_eq {f : E → ℂ} (hf : MemLp f 2) :
    ‖hf.toLp f‖ = (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    ENNReal.toReal_ofReal (by positivity)]
  norm_num

private theorem norm_fourier_pairing_le_L2 {f g : E → ℂ} (hf₁ : Integrable f volume)
    (hf₂ : MemLp f 2) (hg₂ : MemLp g 2) :
    ‖∫ x, 𝓕 f x * g x‖ ≤
      (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫ x, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hF := fourier_ae_eq_L2 hf₁ hf₂
  let F : Lp ℂ 2 (volume : Measure E) := 𝓕 (hf₂.toLp f)
  have hnorm : (∫ x, ‖F x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← norm_toLp_two_eq (Lp.memLp F), Lp.toLp_coeFn]
    exact (Lp.norm_fourier_eq _).trans (norm_toLp_two_eq hf₂)
  have hle := integral_mul_norm_le_Lp_mul_Lq (f := (F : E → ℂ)) (g := g)
    Real.HolderConjugate.two_two
    (by simpa using Lp.memLp F) (by simpa using hg₂)
  calc
    ‖∫ x, 𝓕 f x * g x‖ = ‖∫ x, F x * g x‖ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hF] with x hx using congrArg (· * g x) hx
    _ ≤ ∫ x, ‖F x‖ * ‖g x‖ := by simpa only [norm_mul] using
      norm_integral_le_integral_norm (fun x => F x * g x)
    _ ≤ _ := by rw [← hnorm]; exact hle

/-- Complex powers of a nonnegative amplitude, vanishing identically when the amplitude is zero. -/
private noncomputable def stripPower (a : ℝ) (z : ℂ) : ℂ :=
  if a = 0 then 0 else exp ((Real.log a : ℂ) * (1 - z / 2))

private lemma measurable_stripPower (z : ℂ) : Measurable (stripPower · z) := by
  unfold stripPower
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
    (by fun_prop)

private lemma stripPower_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℂ) :
    stripPower (a * b) z = stripPower a z * stripPower b z := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [stripPower]
  rcases hb.eq_or_lt with rfl | hb
  · simp [stripPower]
  simp only [stripPower, (mul_pos ha hb).ne', ha.ne', hb.ne', ite_false,
    Real.log_mul ha.ne' hb.ne', ofReal_add, add_mul, exp_add]

private lemma norm_stripPower {a : ℝ} {z : ℂ} (ha : 0 ≤ a) (hz : 0 < 1 - z.re / 2) :
    ‖stripPower a z‖ = a ^ (1 - z.re / 2) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [stripPower, Real.zero_rpow hz.ne']
  rw [stripPower, ite_eq_right ha.ne', norm_exp, Real.rpow_def_of_pos ha]
  congr 1
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sub_re, one_re, div_ofNat_re]

private lemma stripPower_ofReal {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 < 1 - t / 2) :
    stripPower a (t : ℂ) = (a ^ (1 - t / 2) : ℝ) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [stripPower, Real.zero_rpow ht.ne']
  rw [stripPower, ite_eq_right ha.ne', Real.rpow_def_of_pos ha, ofReal_exp, ofReal_mul, ofReal_sub,
    ofReal_div, ofReal_one, ofReal_ofNat]

private lemma hasDerivAt_stripPower (a : ℝ) (z : ℂ) :
    HasDerivAt (stripPower a) (stripPower a z * (-(Real.log a : ℂ) / 2)) z := by
  change HasDerivAt (fun w => stripPower a w) _ z
  by_cases ha : a = 0
  · subst a
    simpa [stripPower] using hasDerivAt_const z (0 : ℂ)
  simp only [stripPower, ite_eq_right ha]
  have hd : HasDerivAt (fun w : ℂ => 1 - w / 2) (0 - 1 / 2) z :=
    (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).div_const (2 : ℂ))
  convert ((hd.const_mul (Real.log a : ℂ)).cexp) using 1
  ring

private lemma rpow_le_add {a r : ℝ} (ha : 0 ≤ a) (hr : 1 / 8 ≤ r) (hr' : r ≤ 2) :
    a ^ r ≤ a ^ (1 / 8 : ℝ) + a ^ (2 : ℝ) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [Real.zero_rpow (by linarith : r ≠ 0)]
  rcases le_or_gt a 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge ha h hr).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le h.le hr').trans (le_add_of_nonneg_left (by positivity))

private lemma norm_stripPower_deriv_le {a : ℝ} {z : ℂ} (ha : 0 ≤ a)
    (hz : z ∈ verticalStrip (-1) (3 / 2)) :
    ‖stripPower a z * (-(Real.log a : ℂ) / 2)‖ ≤
      4 * (a ^ (1 / 8 : ℝ) + a ^ (2 : ℝ)) := by
  change -1 < z.re ∧ z.re < 3 / 2 at hz
  set r := 1 - z.re / 2
  have hr : 1 / 4 < r := by dsimp [r]; linarith [hz.2]
  have hr' : r < 3 / 2 := by dsimp [r]; linarith [hz.1]
  rw [norm_mul, norm_stripPower ha (by linarith), norm_div, norm_neg, norm_real,
    Real.norm_eq_abs, Complex.norm_ofNat]
  rcases ha.eq_or_lt with rfl | ha
  · simp
  rcases le_or_gt a 1 with h | h
  · have hlog := Real.neg_rpow_div_le_log ha.le (show 0 < (1 / 8 : ℝ) by norm_num)
    rw [abs_of_nonpos (Real.log_nonpos ha.le h)]
    calc
      a ^ r * (-Real.log a / 2) ≤ a ^ r * (4 * a ^ (-(1 / 8) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * a ^ (r + -(1 / 8)) := by rw [Real.rpow_add ha]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_le_add ha.le (by linarith) (by linarith)) (by norm_num)
  · have hlog := Real.log_le_rpow_div ha.le (show 0 < (1 / 8 : ℝ) by norm_num)
    rw [abs_of_nonneg (Real.log_nonneg h.le)]
    calc
      a ^ r * (Real.log a / 2) ≤ a ^ r * (4 * a ^ (1 / 8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * a ^ (r + 1 / 8) := by rw [Real.rpow_add ha]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_le_add ha.le (by linarith) (by linarith)) (by norm_num)

section ParametricIntegral

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {a : X → ℝ} {k : X → ℂ}

private lemma norm_mul_stripPower_le {a : ℝ} {k z : ℂ} (ha : 0 ≤ a) (hk : ‖k‖ ≤ 1)
    (hz : z ∈ verticalStrip (-1) (3 / 2)) :
    ‖k * stripPower a z‖ ≤ a ^ (1 / 8 : ℝ) + a ^ (2 : ℝ) := by
  change -1 < z.re ∧ z.re < 3 / 2 at hz
  rw [norm_mul, norm_stripPower ha (by linarith [hz.2])]
  exact (mul_le_of_le_one_left (Real.rpow_nonneg ha _) hk).trans
    (rpow_le_add ha (by linarith [hz.2]) (by linarith [hz.1]))

private lemma integrable_mul_stripPower (ha : Measurable a) (hk : Measurable k)
    (ha₀ : ∀ x, 0 ≤ a x) (hk₁ : ∀ x, ‖k x‖ ≤ 1)
    (hi : Integrable (fun x => a x ^ (1 / 8 : ℝ) + a x ^ (2 : ℝ)) μ)
    {z : ℂ} (hz : z ∈ verticalStrip (-1) (3 / 2)) :
    Integrable (fun x => k x * stripPower (a x) z) μ :=
  hi.mono' (hk.mul ((measurable_stripPower z).comp ha)).aestronglyMeasurable
    (ae_of_all _ fun x => norm_mul_stripPower_le (ha₀ x) (hk₁ x) hz)

private lemma differentiableOn_integral_mul_stripPower (ha : Measurable a) (hk : Measurable k)
    (ha₀ : ∀ x, 0 ≤ a x) (hk₁ : ∀ x, ‖k x‖ ≤ 1)
    (hi : Integrable (fun x => a x ^ (1 / 8 : ℝ) + a x ^ (2 : ℝ)) μ) :
    DifferentiableOn ℂ (fun z => ∫ x, k x * stripPower (a x) z ∂μ)
      (verticalStrip (-1) (3 / 2)) := by
  intro z hz
  have hOpen : IsOpen (verticalStrip (-1) (3 / 2)) := isOpen_Ioo.preimage continuous_re
  have hm (w : ℂ) : Measurable (fun x => k x * stripPower (a x) w) :=
    hk.mul ((measurable_stripPower w).comp ha)
  have hm' : Measurable (fun x => (-(Real.log (a x) : ℂ) / 2)) := by fun_prop
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hOpen.mem_nhds hz)
    (Eventually.of_forall fun w => (hm w).aestronglyMeasurable)
    (integrable_mul_stripPower ha hk ha₀ hk₁ hi hz)
    (F' := fun w x => k x * (stripPower (a x) w * (-(Real.log (a x) : ℂ) / 2)))
    ((hk.mul (((measurable_stripPower z).comp ha).mul hm')).aestronglyMeasurable)
    (bound := fun x => 4 * (a x ^ (1 / 8 : ℝ) + a x ^ (2 : ℝ))) ?_
    (hi.const_mul 4) (ae_of_all _ fun x w _ =>
      (hasDerivAt_stripPower (a x) w).const_mul (k x))).2.differentiableAt.differentiableWithinAt
  exact ae_of_all _ fun x w hw => by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hk₁ x)).trans
      (norm_stripPower_deriv_le (ha₀ x) hw)

end ParametricIntegral

private lemma norm_phase_mul_stripPower {a : ℝ} {s z : ℂ} (ha : 0 ≤ a)
    (hs : a ≠ 0 → ‖s‖ = 1) (hz : 0 < 1 - z.re / 2) :
    ‖s * stripPower a z‖ = a ^ (1 - z.re / 2) := by
  rw [norm_mul, norm_stripPower ha hz]
  by_cases h : a = 0
  · simp [h, Real.zero_rpow hz.ne']
  · rw [hs h, one_mul]

private lemma norm_phase_mul_stripPower_sq {a : ℝ} {s z : ℂ} (ha : 0 ≤ a)
    (hs : a ≠ 0 → ‖s‖ = 1) (hz : z.re = 1) :
    ‖s * stripPower a z‖ ^ (2 : ℝ) = a := by
  rw [norm_phase_mul_stripPower ha hs (by rw [hz]; norm_num), hz, ← Real.rpow_mul ha]
  norm_num

private lemma memLp_two_stripPower {u : E → ℝ} {s : E → ℂ} (hu : Measurable u)
    (hs : Measurable s) (hu₀ : ∀ x, 0 ≤ u x) (hs₁ : ∀ x, u x ≠ 0 → ‖s x‖ = 1)
    (hi : Integrable u volume) {z : ℂ} (hz : z.re = 1) :
    MemLp (fun x => s x * stripPower (u x) z) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (hs.mul ((measurable_stripPower z).comp hu)).aestronglyMeasurable).2 ?_
  convert hi using 1
  ext x
  change ‖s x * stripPower (u x) z‖ ^ (2 : ℕ) = u x
  rw [← Real.rpow_natCast]
  exact norm_phase_mul_stripPower_sq (hu₀ x) (hs₁ x) hz

private noncomputable def fourierKernel (x y : E) : ℂ :=
  (Real.fourierChar (-⟪x, y⟫) : ℂ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma continuous_fourierKernel : Continuous (fun w : E × E => fourierKernel w.1 w.2) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_inner (𝕜 := ℝ)).neg)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma norm_fourierKernel (x y : E) : ‖fourierKernel x y‖ = 1 :=
  Circle.norm_coe _

/-- Interpolate the Fourier pairing between the integrable and square-integrable bounds. -/
private theorem norm_fourier_pairing_strip
    {u v : E → ℝ} {s t : E → ℂ} (hu : Measurable u) (hv : Measurable v)
    (hs : Measurable s) (ht : Measurable t)
    (hu₀ : ∀ x, 0 ≤ u x) (hv₀ : ∀ x, 0 ≤ v x)
    (hs₁ : ∀ x, ‖s x‖ ≤ 1) (ht₁ : ∀ x, ‖t x‖ ≤ 1)
    (hs_eq : ∀ x, u x ≠ 0 → ‖s x‖ = 1) (ht_eq : ∀ x, v x ≠ 0 → ‖t x‖ = 1)
    (hu_int : ∀ r : ℝ, 0 < r → Integrable (fun x => u x ^ r) volume)
    (hv_int : ∀ r : ℝ, 0 < r → Integrable (fun x => v x ^ r) volume)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖∫ y, 𝓕 (fun x => s x * stripPower (u x) z) y * (t y * stripPower (v y) z)‖ ≤
      ((∫ x, u x) * (∫ y, v y)) ^ (1 - z.re / 2) := by
  let μ : Measure (E × E) := (volume : Measure E).prod volume
  let a : E × E → ℝ := fun w => u w.1 * v w.2
  let k : E × E → ℂ := fun w => fourierKernel w.1 w.2 * s w.1 * t w.2
  let J (w : ℂ) := fun x => k x * stripPower (a x) w
  let F (w : ℂ) := ∫ x, J w x ∂μ
  have ha : Measurable a := (hu.comp measurable_fst).mul (hv.comp measurable_snd)
  have hk : Measurable k :=
    (continuous_fourierKernel.measurable.mul (hs.comp measurable_fst)).mul (ht.comp measurable_snd)
  have ha₀ (x : E × E) : 0 ≤ a x := mul_nonneg (hu₀ _) (hv₀ _)
  have hk₁ (x : E × E) : ‖k x‖ ≤ 1 := by
    simp only [k, norm_mul, norm_fourierKernel, one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hs₁ _)).trans (ht₁ _)
  have hi (r : ℝ) (hr : 0 < r) : Integrable (fun x => a x ^ r) μ := by
    simpa only [a, Real.mul_rpow (hu₀ _) (hv₀ _)] using (hu_int r hr).mul_prod (hv_int r hr)
  have hbound := (hi (1 / 8) (by norm_num)).add (hi 2 (by norm_num))
  have hJ {w : ℂ} (hw : w ∈ verticalStrip (-1) (3 / 2)) : Integrable (J w) μ :=
    integrable_mul_stripPower ha hk ha₀ hk₁ hbound hw
  have hsub : verticalClosedStrip 0 1 ⊆ verticalStrip (-1) (3 / 2) := by
    intro w hw
    change 0 ≤ w.re ∧ w.re ≤ 1 at hw
    change -1 < w.re ∧ w.re < 3 / 2
    constructor <;> linarith [hw.1, hw.2]
  have hdiff : DiffContOnCl ℂ F (verticalStrip 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [verticalStrip, closure_preimage_re, closure_Ioo zero_ne_one]
    exact (differentiableOn_integral_mul_stripPower ha hk ha₀ hk₁ hbound).mono hsub
  have hbdd : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    refine ⟨∫ x, (a x ^ (1 / 8 : ℝ) + a x ^ (2 : ℝ)) ∂μ, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono_ae (hJ (hsub hw)).norm hbound (ae_of_all _ fun x => ?_))
    exact norm_mul_stripPower_le (ha₀ x) (hk₁ x) (hsub hw)
  have hpair {w : ℂ} (hw : w ∈ verticalClosedStrip 0 1) :
      F w = ∫ y, 𝓕 (fun x => s x * stripPower (u x) w) y * (t y * stripPower (v y) w) := by
    change (∫ x, J w x ∂μ) = _
    rw [integral_prod_symm _ (hJ (hsub hw))]
    congr with y
    rw [Real.fourier_eq, ← integral_mul_const]
    congr with x
    rw [show J w (x, y) = fourierKernel x y * s x * t y * stripPower (u x * v y) w by rfl,
      stripPower_mul (hu₀ x) (hv₀ y), Circle.smul_def, smul_eq_mul]
    unfold fourierKernel
    ring
  have hu_int₁ : Integrable u volume := by simpa only [Real.rpow_one] using hu_int 1 zero_lt_one
  have hv_int₁ : Integrable v volume := by simpa only [Real.rpow_one] using hv_int 1 zero_lt_one
  let A := ∫ x, u x
  let B := ∫ y, v y
  have hA : 0 ≤ A := integral_nonneg hu₀
  have hB : 0 ≤ B := integral_nonneg hv₀
  have hleft : ∀ w ∈ re ⁻¹' {0}, ‖F w‖ ≤ A * B := by
    intro w hw
    have hw₀ : w.re = 0 := hw
    have hw' : w ∈ verticalClosedStrip 0 1 := by
      change 0 ≤ w.re ∧ w.re ≤ 1
      rw [hw₀]
      norm_num
    rw [show A * B = ∫ x, a x ∂μ from (integral_prod_mul u v).symm]
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono_ae (hJ (hsub hw')).norm (hu_int₁.mul_prod hv_int₁) (ae_of_all _ fun x => ?_))
    change ‖k x * stripPower (a x) w‖ ≤ a x
    rw [norm_mul, norm_stripPower (ha₀ x) (by rw [hw₀]; norm_num), hw₀]
    simp only [zero_div, sub_zero, Real.rpow_one]
    exact mul_le_of_le_one_left (ha₀ x) (hk₁ x)
  have hright : ∀ w ∈ re ⁻¹' {1}, ‖F w‖ ≤ (A * B) ^ (1 / 2 : ℝ) := by
    intro w hw
    have hw₁ : w.re = 1 := hw
    have hw' : w ∈ verticalClosedStrip 0 1 := by
      change 0 ≤ w.re ∧ w.re ≤ 1
      rw [hw₁]
      norm_num
    have hL1 : Integrable (fun x => s x * stripPower (u x) w) volume :=
      integrable_mul_stripPower hu hs hu₀ hs₁
        ((hu_int (1 / 8) (by norm_num)).add (hu_int 2 (by norm_num))) (hsub hw')
    have hL2 := memLp_two_stripPower hu hs hu₀ hs_eq hu_int₁ hw₁
    have hL2' := memLp_two_stripPower hv ht hv₀ ht_eq hv_int₁ hw₁
    rw [hpair hw', Real.mul_rpow hA hB]
    refine (norm_fourier_pairing_le_L2 hL1 hL2 hL2').trans_eq ?_
    simp_rw [norm_phase_mul_stripPower_sq (hu₀ _) (hs_eq _) hw₁,
      norm_phase_mul_stripPower_sq (hv₀ _) (ht_eq _) hw₁, A, B]
  rw [← hpair hz]
  have h := norm_le_interp_of_mem_verticalClosedStrip₀₁' F hz hdiff hbdd hleft hright
  change 0 ≤ z.re ∧ z.re ≤ 1 at hz
  have hsum : 1 - z.re + (1 / 2) * z.re = 1 - z.re / 2 := by ring
  rw [← Real.rpow_mul (mul_nonneg hA hB),
    ← Real.rpow_add' (mul_nonneg hA hB) (by linarith [hz.2] : 1 - z.re + 1 / 2 * z.re ≠ 0),
    hsum] at h
  exact h

private noncomputable def phase (c : ℂ) : ℂ :=
  c / (‖c‖ : ℂ)

private lemma measurable_phase : Measurable phase := by
  unfold phase
  fun_prop

private lemma norm_phase_of_ne_zero {c : ℂ} (hc : c ≠ 0) : ‖phase c‖ = 1 := by
  simp [phase, Complex.norm_real, norm_ne_zero_iff.mpr hc]

private lemma norm_phase_le_one (c : ℂ) : ‖phase c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [phase, hc]
  · rw [norm_phase_of_ne_zero hc]

private lemma phase_mul_norm (c : ℂ) : phase c * (‖c‖ : ℂ) = c := by
  by_cases hc : c = 0
  · simp [phase, hc]
  · exact div_mul_cancel₀ c (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc))

private lemma mul_conj_phase (c : ℂ) : c * conj (phase c) = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · simp [hc]
  rw [phase, map_div₀, conj_ofReal, ← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    ofReal_pow, sq, mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc))]

private lemma integrable_schwartz_rpow (f : SchwartzMap E ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => ‖f x‖ ^ r) volume := by
  simpa only [ENNReal.toReal_ofReal hr.le] using (f.memLp (ENNReal.ofReal r)).integrable_norm_rpow
    (by simp [hr]) (by simp)

private theorem norm_fourier_toLp_le (f : SchwartzMap E ℂ) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hpq : p.HolderConjugate q) :
    ‖(𝓕 f).toLp q‖ ≤ ‖f.toLp p‖ := by
  let _ := hpq
  rcases hp.eq_or_lt with rfl | hp
  · rw [ENNReal.HolderConjugate.unique 1 q ⊤]
    exact f.norm_fourier_Lp_top_leq_toLp_one
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hp₂
  have hp₁ : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).mpr hp
  have hq := ENNReal.HolderConjugate.toReal hp₁ (q := q)
  have hqt : q ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hq.symm.pos).2.ne
  have hp₂' : p.toReal ≤ 2 := by
    simpa using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hp₂
  let θ : ℝ := 2 * (1 - p.toReal⁻¹)
  have hθ : 1 - θ / 2 = p.toReal⁻¹ := by dsimp [θ]; ring
  have hp_inv : 0 < p.toReal⁻¹ := inv_pos.mpr hq.pos
  have hθ_mem : (θ : ℂ) ∈ verticalClosedStrip 0 1 := by
    change 0 ≤ (θ : ℂ).re ∧ (θ : ℂ).re ≤ 1
    rw [ofReal_re]
    have h₀ := inv_le_one_of_one_le₀ hp₁.le
    have h₁ : (2 : ℝ)⁻¹ ≤ p.toReal⁻¹ := inv_anti₀ hq.pos hp₂'
    constructor <;> linarith [hθ]
  have hpq' : 1 + q.toReal * p.toReal⁻¹ = q.toReal := by
    calc
      1 + q.toReal * p.toReal⁻¹ = q.toReal * (p.toReal⁻¹ + q.toReal⁻¹) := by
        rw [mul_add, mul_inv_cancel₀ hq.symm.pos.ne', add_comm]
      _ = q.toReal := by rw [hq.inv_add_inv_eq_one, mul_one]
  -- The Fourier transform is Schwartz, so both amplitudes have integrable positive powers.
  let g := 𝓕 f
  let u : E → ℝ := fun x => ‖f x‖ ^ p.toReal
  let v : E → ℝ := fun x => ‖g x‖ ^ q.toReal
  let s : E → ℂ := fun x => phase (f x)
  let t : E → ℂ := fun x => conj (phase (g x))
  have hu : Measurable u := by dsimp [u]; fun_prop
  have hv : Measurable v := by dsimp [v]; fun_prop
  have hs : Measurable s := measurable_phase.comp f.continuous.measurable
  have ht : Measurable t :=
    Complex.continuous_conj.measurable.comp (measurable_phase.comp g.continuous.measurable)
  have hu₀ (x : E) : 0 ≤ u x := Real.rpow_nonneg (norm_nonneg _) _
  have hv₀ (x : E) : 0 ≤ v x := Real.rpow_nonneg (norm_nonneg _) _
  have hs₁ (x : E) : ‖s x‖ ≤ 1 := norm_phase_le_one _
  have ht₁ (x : E) : ‖t x‖ ≤ 1 := by simpa [t] using norm_phase_le_one (g x)
  have hs_eq (x : E) (h : u x ≠ 0) : ‖s x‖ = 1 := by
    apply norm_phase_of_ne_zero
    intro hfx
    exact h (by simp [u, hfx, Real.zero_rpow hq.pos.ne'])
  have ht_eq (x : E) (h : v x ≠ 0) : ‖t x‖ = 1 := by
    change ‖conj (phase (g x))‖ = 1
    rw [norm_conj]
    apply norm_phase_of_ne_zero
    intro hgx
    exact h (by simp [v, hgx, Real.zero_rpow hq.symm.pos.ne'])
  have hu_int (r : ℝ) (hr : 0 < r) : Integrable (fun x => u x ^ r) volume := by
    simp_rw [u, ← Real.rpow_mul (norm_nonneg _)]
    exact integrable_schwartz_rpow f (mul_pos hq.pos hr)
  have hv_int (r : ℝ) (hr : 0 < r) : Integrable (fun x => v x ^ r) volume := by
    simp_rw [v, ← Real.rpow_mul (norm_nonneg _)]
    exact integrable_schwartz_rpow g (mul_pos hq.symm.pos hr)
  have h := norm_fourier_pairing_strip hu hv hs ht hu₀ hv₀ hs₁ ht₁ hs_eq ht_eq hu_int hv_int hθ_mem
  -- At the interpolation parameter the second factor attains the Hölder pairing.
  have hf : (fun x => s x * stripPower (u x) (θ : ℂ)) = (f : E → ℂ) := by
    funext x
    rw [stripPower_ofReal (hu₀ x) (hθ.symm ▸ hp_inv), hθ]
    change phase (f x) * ((‖f x‖ ^ p.toReal) ^ p.toReal⁻¹ : ℝ) = f x
    rw [Real.rpow_rpow_inv (norm_nonneg _) hq.pos.ne']
    exact phase_mul_norm _
  have hg (x : E) : 𝓕 (f : E → ℂ) x * (t x * stripPower (v x) (θ : ℂ)) = (v x : ℂ) := by
    rw [stripPower_ofReal (hv₀ x) (hθ.symm ▸ hp_inv), hθ, ← SchwartzMap.fourier_coe]
    change g x * (conj (phase (g x)) * ((‖g x‖ ^ q.toReal) ^ p.toReal⁻¹ : ℝ)) = (v x : ℂ)
    have hexp : 1 + q.toReal * p.toReal⁻¹ ≠ 0 := hpq'.trans_ne hq.symm.pos.ne'
    have hpow : ‖g x‖ * ‖g x‖ ^ (q.toReal * p.toReal⁻¹) = v x := by
      change _ = ‖g x‖ ^ q.toReal
      conv_lhs =>
        arg 1
        rw [← Real.rpow_one ‖g x‖]
      rw [← Real.rpow_add' (norm_nonneg _) hexp, hpq']
    rw [← mul_assoc, mul_conj_phase, ← ofReal_mul, ← Real.rpow_mul (norm_nonneg _), hpow]
  rw [hf] at h
  have hvIntegral : 0 ≤ ∫ x, v x := integral_nonneg hv₀
  simp_rw [hg, integral_complex_ofReal, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hvIntegral, ofReal_re, hθ] at h
  let A := ∫ x, u x
  let B := ∫ x, v x
  have hA : 0 ≤ A := integral_nonneg hu₀
  have hB : 0 ≤ B := integral_nonneg hv₀
  have hineq : B ≤ (A * B) ^ p.toReal⁻¹ := h
  rw [SchwartzMap.norm_toLp' (ENNReal.toReal_pos_iff.mp hq.symm.pos).1.ne' hqt,
    SchwartzMap.norm_toLp' (ENNReal.toReal_pos_iff.mp hq.pos).1.ne' hpt]
  change B ^ q.toReal⁻¹ ≤ A ^ p.toReal⁻¹
  by_cases hB₀ : B = 0
  · rw [hB₀, Real.zero_rpow (inv_ne_zero hq.symm.pos.ne')]
    positivity
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB₀)
  apply (le_of_mul_le_mul_right · (Real.rpow_pos_of_pos hBpos p.toReal⁻¹))
  rw [← Real.rpow_add hBpos, add_comm q.toReal⁻¹, hq.inv_add_inv_eq_one, Real.rpow_one,
    ← Real.mul_rpow hA hB]
  exact hineq

/-- **Hausdorff–Young inequality for Schwartz functions.** Let $n$ be a natural number and let
$\mathcal{F}$ be the Fourier transform on $\mathbb{R}^n$,
$\mathcal{F}f(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle x, \xi \rangle}\, dx$. There is a
constant $C > 0$ such that for all $p, p' \in [0, \infty]$ with $1 \le p \le 2$ and
$\frac{1}{p} + \frac{1}{p'} = 1$ (so $p' = \infty$ when $p = 1$) and every complex-valued
Schwartz function $f$ on $\mathbb{R}^n$, $\|\mathcal{F}f\|_{L^{p'}} \le C \|f\|_{L^p}$, where the
$L^p$ norms are taken with respect to Lebesgue measure on $\mathbb{R}^n$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_84.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_norm_fourier_toLp_le_norm_toLp_of_holderConjugate
    {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ p p' : ENNReal,
        1 ≤ p → p ≤ 2 → ENNReal.HolderConjugate p p' →
          ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
            ‖(𝓕 f).toLp p'
                (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖ ≤
              C * ‖f.toLp p
                (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖ := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro p p' hp hp₂ hpq f
  rw [one_mul]
  exact norm_fourier_toLp_le f hp hp₂ hpq

end MathlibExt.Analysis.Fourier.HausdorffYoungSchwartzWanted
