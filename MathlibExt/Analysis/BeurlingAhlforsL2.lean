/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`Mathlib/Analysis/Calculus/Rademacher.lean` (Mathlib), for the localized translation estimate
in the proof of `fourier_direction`:
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sébastien Gouëzel
-/

module

public import MathlibExt.Analysis.BeurlingAhlfors
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Beurling–Ahlfors transform on $L^2$

The circular principal value has operator norm one (`l2Norm_wanted`). Its Fourier multiplier
$\bar\xi/\xi$ has modulus one almost everywhere, so Plancherel gives an isometry on $L^2$.

To identify this isometry with the principal value, we use the disk-average formula from the
proof of Theorem 3 in [Mateu and Verdera](https://arxiv.org/abs/math/0603077), with the kernel
sign of `beurlingTrunc`. The function equal to $z/r^2$ inside a disk and $1/\bar z$ outside
has the disk indicator and the conjugated truncated kernel as its two Wirtinger derivatives,
up to normalization. Differentiating the difference of two such functions gives a compactly
supported Fourier calculation. Letting the outer radius grow identifies each truncation with a
disk average of the isometry. Lebesgue differentiation then yields the principal value.
-/

open MeasureTheory Filter Topology FourierTransform Metric Real
open scoped ComplexConjugate ENNReal NNReal SchwartzMap ContDiff RealInnerProductSpace

namespace MathlibExt.Analysis.BeurlingAhlforsWanted

noncomputable section

open BeurlingAhlfors

private abbrev H := Lp (α := ℂ) ℂ 2

private def symbol (ξ : ℂ) : ℂ := conj ξ / ξ

private theorem symbol_norm : ∀ᵐ ξ : ℂ, ‖symbol ξ‖ = 1 := by
  filter_upwards [volume.ae_ne (0 : ℂ)] with ξ hξ
  simp [symbol, hξ]

private theorem memLp_symbol_mul (g : H) : MemLp (fun ξ ↦ symbol ξ * g ξ) 2 volume := by
  refine (Lp.memLp g).congr_norm ?_ ?_
  · exact ((Complex.continuous_conj.measurable.div measurable_id).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g)
  · filter_upwards [symbol_norm] with ξ hξ
    simp [hξ]

private def transform (g : H) : H :=
  𝓕⁻ ((memLp_symbol_mul (𝓕 g)).toLp _)

private theorem transform_norm (g : H) : ‖transform g‖ = ‖g‖ := by
  rw [← Lp.norm_fourier_eq (transform g)]
  simp only [transform, fourier_fourierInv_eq, Lp.norm_toLp]
  rw [eLpNorm_congr_norm_ae (memLp_symbol_mul (𝓕 g)).aestronglyMeasurable
    (Lp.aestronglyMeasurable (𝓕 g)) ?_]
  · exact Lp.norm_fourier_eq g
  · filter_upwards [symbol_norm] with ξ hξ
    simp [hξ]

private theorem fourier_coe_ae {f : ℂ → ℂ} (h : MemLp f 2 volume) (hi : Integrable f) :
    ⇑(𝓕 (h.toLp f) : H) =ᵐ[(volume : Measure ℂ)] (𝓕 f : ℂ → ℂ) := by
  let G : H := 𝓕 (h.toLp f)
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp G).locallyIntegrable (by norm_num))
  · exact (VectorFourier.fourierIntegral_continuous continuous_fourierChar
      (innerSL ℝ (E := ℂ)).continuous₂ hi).locallyIntegrable
  intro g hg hgc
  let φ := (hgc.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  have he := congrArg (fun T : 𝓢'(ℂ, ℂ) ↦ T φ) (Lp.fourier_toTemperedDistribution_eq (h.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at he
  have hp : ∫ x, (𝓕 φ) x * f x = ∫ x, φ x * 𝓕 f x := by
    have hpair := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℂ) (ν := volume) (μ := volume)
      continuous_fourierChar continuous_inner φ.integrable hi
    rw [flip_innerₗ] at hpair
    exact hpair
  change (∫ x, φ x * G x) = ∫ x, φ x * 𝓕 f x
  exact he.symm.trans ((integral_congr_ae (h.coeFn_toLp.mono
    (fun x hx ↦ congrArg (fun c : ℂ ↦ (𝓕 φ) x * c) hx))).trans hp)

private theorem char_deriv (a : ℝ) (M : ℂ) :
    HasDerivAt (fun t : ℝ ↦ (fourierChar (t * a) : ℂ) * M)
      ((2 * π * Complex.I * a) * M) 0 := by
  have hArg : HasDerivAt (fun t : ℝ ↦ t * a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const a
  have hc := HasDerivAt.scomp (h := fun t : ℝ ↦ t * a) (g₁ := fun x : ℝ ↦ (fourierChar x : ℂ))
    0 (hasDerivAt_fourierChar (0 * a)) hArg
  apply (hc.mul_const M).congr_deriv
  simp [Complex.real_smul, mul_comm, mul_left_comm]

private theorem fourier_direction {U D : ℂ → ℂ} {C : ℝ≥0}
    (hU : HasCompactSupport U) (hL : LipschitzWith C U)
    (v ξ : ℂ) (hm : AEStronglyMeasurable D volume)
    (hd : ∀ᵐ x : ℂ, HasLineDerivAt ℝ U (D x) x v) :
    𝓕 D ξ = (2 * π * Complex.I * inner ℝ v ξ) * 𝓕 U ξ := by
  let e (x : ℂ) := (fourierChar (-inner ℝ x ξ) : ℂ)
  have ec : Continuous e := by dsimp [e]; fun_prop
  -- For translations of size at most one in parameter space, this compact set
  -- contains the supports of both the original and translated integrands.
  let K := Metric.cthickening ‖v‖ (tsupport U)
  have hK : IsCompact K := IsCompact.cthickening hU
  let L := (C * ‖v‖₊ : ℝ≥0)
  let F (t : ℝ) (x : ℂ) := e x * U (x + t • v)
  have hF : ∀ t, Continuous (F t) := fun t ↦ ec.mul
    (hL.continuous.comp (continuous_add_const _))
  have hb : Integrable (K.indicator fun _ ↦ (L : ℝ)) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_lt_top.ne
  have hdiff : HasDerivAt (fun t ↦ ∫ x, F t x) (𝓕 D ξ) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_lip
      (F := F) (F' := fun x ↦ e x * D x) (ball_mem_nhds 0 one_pos)
      (.of_forall fun t ↦ (hF t).aestronglyMeasurable) ?_ (ec.aestronglyMeasurable.mul hm)
      ?_ hb ?_).2
    · simpa [F, Pi.mul_def] using (ec.mul hL.continuous).integrable_of_hasCompactSupport hU.mul_left
    · apply ae_of_all
      intro x
      by_cases hx : x ∈ K
      · simp only [Set.indicator_of_mem hx, Real.nnabs_coe]
        apply LipschitzOnWith.of_dist_le_mul
        intro s _ t _
        calc
          dist (F s x) (F t x) = dist (U (x + s • v)) (U (x + t • v)) := by
            simp [F, e, dist_eq_norm, ← mul_sub]
          _ ≤ C * dist (x + s • v) (x + t • v) := hL.dist_le_mul _ _
          _ = L * dist s t := by
            rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, dist_eq_norm]
            simp [L, mul_left_comm, mul_comm]
      · simp only [Set.indicator_of_notMem hx]
        apply LipschitzOnWith.of_dist_le_mul
        have hzero {s : ℝ} (hs : s ∈ ball 0 1) : F s x = 0 := by
          suffices x + s • v ∉ tsupport U from
            mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport this)
          intro h
          apply hx (mem_cthickening_of_dist_le _ _ _ _ h ?_)
          simpa [dist_eq_norm] using mul_le_of_le_one_left (norm_nonneg v)
            (show ‖s‖ ≤ 1 from (mem_ball_zero_iff.mp hs).le)
        intro s hs t ht
        simp [hzero hs, hzero ht]
    · filter_upwards [hd] with x hx using hx.const_mul (e x)
  have hFourier (t : ℝ) : (∫ x, F t x) =
      (fourierChar (t * inner ℝ v ξ) : ℂ) * 𝓕 U ξ := by
    change 𝓕 (U ∘ (fun x ↦ x + t • v)) ξ = _
    calc
      _ = fourierChar (inner ℝ (t • v) ξ) • 𝓕 U ξ :=
        congrFun (VectorFourier.fourierIntegral_comp_add_right fourierChar volume
          (innerₗ ℂ) U (t • v)) ξ
      _ = _ := by rw [real_inner_smul_left]; rfl
  exact hdiff.unique <| (char_deriv (inner ℝ v ξ) (𝓕 U ξ)).congr_of_eventuallyEq
    (.of_forall hFourier)

-- These are the conjugates of the primitive and kernel used in the integral,
-- so that their pairings with the input are complex Hilbert space inner products.
private def primitive (r : ℝ) (z : ℂ) : ℂ := z / ((max r ‖z‖ : ℝ) : ℂ) ^ 2

private def disk (r : ℝ) (z : ℂ) : ℂ := if ‖z‖ ≤ r then ((r : ℂ) ^ 2)⁻¹ else 0

private def kernel (r : ℝ) (z : ℂ) : ℂ := if r < ‖z‖ then -((conj z) ^ 2)⁻¹ else 0

private theorem primitive_outside {r : ℝ} {z : ℂ} (hz : r ≤ ‖z‖) :
    primitive r z = (conj z)⁻¹ := by
  rw [primitive, max_eq_right hz, ← Complex.ofReal_pow, Complex.sq_norm, ← Complex.mul_conj]
  by_cases h : z = 0
  · simp [h]
  field_simp

private theorem primitive_lip {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal (3 / r ^ 2)) (primitive r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  let a := max r ‖x‖
  let b := max r ‖y‖
  have ha : 0 < a := hr.trans_le (le_max_left ..)
  have hb : 0 < b := hr.trans_le (le_max_left ..)
  have hab : |b - a| ≤ ‖x - y‖ := by
    simpa [a, b, dist_eq_norm, norm_sub_rev y x] using
      ((lipschitzWith_one_norm (E := ℂ)).const_max r).dist_le_mul y x
  have hsplit : primitive r x - primitive r y = (x - y) / (a : ℂ) ^ 2 +
      (y / b) * ((b - a : ℝ) / (a : ℂ)) * ((a : ℂ)⁻¹ + (b : ℂ)⁻¹) := by
    change x / (a : ℂ) ^ 2 - y / (b : ℂ) ^ 2 = _
    push_cast
    field_simp [ha.ne', hb.ne']
    ring
  have h1 : ‖y / (b : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb, div_le_one hb]
    exact le_max_right _ _
  have inva : a⁻¹ ≤ r⁻¹ := inv_anti₀ hr (le_max_left ..)
  have invb : b⁻¹ ≤ r⁻¹ := inv_anti₀ hr (le_max_left ..)
  rw [hsplit]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ ‖x - y‖ / r ^ 2 + (1 * (‖x - y‖ / r)) * (r⁻¹ + r⁻¹) := by
      rw [norm_mul, norm_mul, norm_div, norm_pow]
      refine add_le_add ?_ (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
      · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
        gcongr
        exact le_max_left _ _
      · refine mul_le_mul h1 ?_ (norm_nonneg _) zero_le_one
        rw [norm_div]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
        gcongr
        exact le_max_left _ _
      · refine (norm_add_le _ _).trans ?_
        simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
          abs_of_pos hb] using add_le_add inva invb
    _ = _ := by ring

private theorem primitive_deriv {r : ℝ} (hr : 0 < r) (v : ℂ) :
    ∀ᵐ z : ℂ, HasLineDerivAt ℝ (primitive r)
      (disk r z * v + kernel r z * conj v) z v := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (Measure.addHaar_sphere (volume : Measure ℂ) 0 r)] with z hz
  have hn : ‖z‖ ≠ r := by simpa [Metric.mem_sphere] using hz
  have H : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  rcases lt_or_gt_of_ne hn with hin | hout
  · simp only [disk, ite_eq_left hin.le, kernel, ite_eq_right hin.not_gt, zero_mul, add_zero]
    refine (H.div_const ((r : ℂ) ^ 2)).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · have hev : ∀ᶠ t : ℝ in 𝓝 0, ‖z + t • v‖ < r :=
        (show Continuous (fun t : ℝ ↦ ‖z + t • v‖) by fun_prop).continuousAt.eventually_lt
          continuousAt_const (by simpa)
      filter_upwards [hev] with t ht using by simp only [primitive, max_eq_left ht.le]
    · ring
  · simp only [disk, ite_eq_right hout.not_ge, kernel, ite_eq_left hout, zero_mul, zero_add]
    have hzero : conj z ≠ 0 := by
      by_cases hz0 : z = 0
      · subst z
        simp at hout
        linarith
      simpa using hz0
    have hc : HasDerivAt (fun t : ℝ ↦ conj z + t • conj v) (conj v) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (conj v)).const_add (conj z)
    have hval : conj z + (0 : ℝ) • conj v ≠ 0 := by simpa using hzero
    have hi := (hasDerivAt_inv hval).scomp (0 : ℝ) hc
    refine hi.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · have hev : ∀ᶠ t : ℝ in 𝓝 0, r < ‖z + t • v‖ :=
        continuousAt_const.eventually_lt
          (show Continuous (fun t : ℝ ↦ ‖z + t • v‖) by fun_prop).continuousAt (by simpa)
      filter_upwards [hev] with t ht using by rw [primitive_outside ht.le]; simp
    · simp [mul_comm]

private theorem disk_mem (r : ℝ) : MemLp (disk r) 2 volume := by
  convert! memLp_indicator_const (μ := (volume : Measure ℂ)) 2
    (s := closedBall 0 r) measurableSet_closedBall.nullMeasurableSet
    (((r : ℂ) ^ 2)⁻¹) (Or.inr measure_closedBall_lt_top.ne) using 1
  ext z
  simp [disk, Set.indicator]

private theorem kernel_mem {r : ℝ} (hr : 0 < r) : MemLp (kernel r) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by
    apply Measurable.aestronglyMeasurable
    exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) (by fun_prop)
      measurable_const)).2
  -- In polar coordinates the squared kernel has radial density t⁻³ outside the disk.
  let a (t : ℝ) := if r < t then (t ^ 4)⁻¹ else 0
  have hh : Integrable (fun z : ℂ ↦ a ‖z‖) := by
    rw [integrable_fun_norm_addHaar volume]
    have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hr)
    have hI := (integrable_indicator_iff measurableSet_Ioi).2 hi
    apply hI.integrableOn.congr_fun _ measurableSet_Ioi
    intro t ht
    by_cases hrt : r < t
    · have ht' : t ≠ 0 := (hr.trans hrt).ne'
      simp [Set.indicator, a, hrt, Real.rpow_neg (hr.trans hrt).le,
        show (-3 : ℝ) = -(3 : ℕ) by norm_num]
      field_simp
    · simp [Set.indicator, a, hrt]
  apply hh.congr
  filter_upwards with z
  by_cases h : r < ‖z‖
  · simp [a, kernel, h, ← pow_mul]
  · simp [a, kernel, h]

private theorem integrable_compact_of_l2 {f : ℂ → ℂ} (h : MemLp f 2 volume)
    (hc : HasCompactSupport f) : Integrable f := by
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).1
  exact (h.locallyIntegrable (by norm_num)).integrableOn_isCompact hc

private theorem annulus_fourier {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    Integrable (disk r - disk R) ∧ Integrable (kernel r - kernel R) ∧
    ∀ ξ : ℂ, 𝓕 (kernel r - kernel R) ξ * conj ξ = 𝓕 (disk r - disk R) ξ * ξ := by
  let U := primitive r - primitive R
  let b := disk r - disk R
  let k := kernel r - kernel R
  let s := closedBall (0 : ℂ) (max r R)
  have hout {z : ℂ} (hz : z ∉ s) : r < ‖z‖ ∧ R < ‖z‖ := by
    simpa [s] using hz
  have hc : HasCompactSupport U := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (max r R)) fun z hz ↦ ?_
    obtain ⟨h1, h2⟩ := hout hz
    simp [U, primitive_outside h1.le, primitive_outside h2.le]
  have hb : Integrable b := by
    apply integrable_compact_of_l2 ((disk_mem r).sub (disk_mem R))
    refine HasCompactSupport.intro (isCompact_closedBall 0 (max r R)) fun z hz ↦ ?_
    obtain ⟨h1, h2⟩ := hout hz
    simp [disk, h1.not_ge, h2.not_ge]
  have hk : Integrable k := by
    apply integrable_compact_of_l2 ((kernel_mem hr).sub (kernel_mem hR))
    refine HasCompactSupport.intro (isCompact_closedBall 0 (max r R)) fun z hz ↦ ?_
    obtain ⟨h1, h2⟩ := hout hz
    simp [kernel, h1, h2]
  refine ⟨hb, hk, ?_⟩
  intro ξ
  have h (v : ℂ) : 𝓕 b ξ * v + 𝓕 k ξ * conj v =
      2 * π * Complex.I * (inner ℝ v ξ : ℝ) * 𝓕 U ξ := by
    let D (z : ℂ) := b z * v + k z * conj v
    have hderiv : ∀ᵐ z : ℂ, HasLineDerivAt ℝ U (D z) z v := by
      filter_upwards [primitive_deriv hr v, primitive_deriv hR v] with z h1 h2
      have he : D z = (disk r z * v + kernel r z * conj v) -
          (disk R z * v + kernel R z * conj v) := by simp [D, b, k, sub_mul]; ring
      rw [he]
      exact h1.sub h2
    rw [← fourier_direction hc ((primitive_lip hr).sub (primitive_lip hR)) v ξ
      (D := D) ((hb.mul_const v).add (hk.mul_const (conj v))).aestronglyMeasurable hderiv]
    rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
    simp only [D, Circle.smul_def, smul_eq_mul, mul_add, ← mul_assoc]
    rw [integral_add, integral_mul_const, integral_mul_const]
    · exact ((Real.fourierIntegral_convergent_iff ξ).2 hb).mul_const v
    · exact ((Real.fourierIntegral_convergent_iff ξ).2 hk).mul_const (conj v)
  -- The real and imaginary directions recover the two Wirtinger derivatives.
  have h1 := h 1
  have hi := h Complex.I
  simp only [mul_one, map_one, Complex.inner] at h1
  simp only [Complex.conj_I, mul_neg, Complex.inner, Complex.neg_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub, neg_neg] at hi
  change 𝓕 k ξ * conj ξ = 𝓕 b ξ * ξ
  have ex : ξ = (ξ.re : ℂ) + ξ.im * Complex.I := (Complex.re_add_im ξ).symm
  conv_lhs => arg 2; rw [ex]
  conv_rhs => arg 2; rw [ex]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (norm := (ring_nf; simp [Complex.I_sq]))
    -(ξ.im : ℂ) * Complex.I * h1 + (ξ.re : ℂ) * Complex.I * hi

private theorem inner_pair {b k : ℂ → ℂ} (bi : Integrable b) (ki : Integrable k)
    (bm : MemLp b 2 volume) (km : MemLp k 2 volume)
    (rel : ∀ ξ : ℂ, 𝓕 k ξ * conj ξ = 𝓕 b ξ * ξ) (F : H) :
    inner ℂ (km.toLp k) F = inner ℂ (bm.toLp b) (transform F) := by
  rw [← Lp.inner_fourier_eq (km.toLp k) F, ← Lp.inner_fourier_eq (bm.toLp b) (transform F)]
  simp only [transform, fourier_fourierInv_eq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourier_coe_ae bm bi, fourier_coe_ae km ki, (memLp_symbol_mul (𝓕 F)).coeFn_toLp,
    volume.ae_ne (0 : ℂ)] with ξ hb hk hm hξ
  simp only [RCLike.inner_apply, hb, hk, hm]
  simp only [symbol]
  have hc := congrArg (conj : ℂ → ℂ) (rel ξ)
  simp only [map_mul, Complex.conj_conj] at hc
  field_simp [hξ]
  linear_combination (𝓕 F) ξ * hc

private theorem fourier_shift (u : ℂ → ℂ) (z ξ : ℂ) :
    𝓕 (fun w ↦ u (w + z)) ξ = (fourierChar (inner ℝ z ξ) : ℂ) * 𝓕 u ξ :=
  congrFun (VectorFourier.fourierIntegral_comp_add_right fourierChar volume (innerₗ ℂ) u z) ξ

private theorem annulus_pair {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z : ℂ)
    (F : H) :
    ∫ w, F w * conj ((kernel r - kernel R) (w - z)) =
      ∫ w, (transform F) w * conj ((disk r - disk R) (w - z)) := by
  obtain ⟨bi, ki, rel⟩ := annulus_fourier hr hR
  let s (w : ℂ) := w + -z
  have hs : MeasurePreserving s volume volume := measurePreserving_add_right volume (-z)
  let b := (disk r - disk R) ∘ s
  let k := (kernel r - kernel R) ∘ s
  have bm : MemLp b 2 volume := ((disk_mem r).sub (disk_mem R)).comp_measurePreserving hs
  have km : MemLp k 2 volume := ((kernel_mem hr).sub (kernel_mem hR)).comp_measurePreserving hs
  have he := inner_pair (bi.comp_add_right (-z)) (ki.comp_add_right (-z)) bm km
    (fun ξ ↦ by
      change 𝓕 (fun w ↦ (kernel r - kernel R) (w + -z)) ξ * _ =
        𝓕 (fun w ↦ (disk r - disk R) (w + -z)) ξ * _
      rw [fourier_shift, fourier_shift, mul_assoc, rel, ← mul_assoc]) F
  simp only [L2.inner_def, RCLike.inner_apply] at he
  have hsub (u : ℂ → ℂ) (hu : MemLp (u ∘ s) 2 volume) (g : H) :
      ∫ w, g w * conj (u (w - z)) = ∫ w, g w * conj (hu.toLp _ w) := by
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with w hw
    simp [hw, s, sub_eq_add_neg]
  exact (hsub _ km F).trans (he.trans (hsub _ bm (transform F)).symm)

private def envelope (w : ℂ) : ℝ := ‖disk 1 w‖ + ‖kernel 1 w‖

private theorem cutoff_bounds (R : ℝ) (hR : 1 ≤ R) (w : ℂ) :
    ‖disk R w‖ ≤ envelope w ∧ ‖kernel R w‖ ≤ envelope w := by
  have hd (r : ℝ) : ‖disk r w‖ = if ‖w‖ ≤ r then (r ^ 2)⁻¹ else 0 := by
    by_cases h : ‖w‖ ≤ r <;> simp [disk, h, sq_abs]
  have hk (r : ℝ) : ‖kernel r w‖ = if r < ‖w‖ then (‖w‖ ^ 2)⁻¹ else 0 := by
    by_cases h : r < ‖w‖ <;> simp [kernel, h]
  simp only [envelope, hd, hk]
  by_cases hw : ‖w‖ ≤ 1
  · simpa [hw, hw.trans hR, hw.not_gt, (hw.trans hR).not_gt] using
      inv_le_one_of_one_le₀ (one_le_pow₀ hR (n := 2))
  by_cases hwR : ‖w‖ ≤ R
  · simpa [hw, not_le.mp hw, hwR, hwR.not_gt] using
      inv_anti₀ (sq_pos_of_pos (zero_lt_one.trans (not_le.mp hw)))
        (show ‖w‖ ^ 2 ≤ R ^ 2 by gcongr)
  · simp [hw, not_le.mp hw, hwR, not_le.mp hwR]

private theorem shift_mem {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : MemLp f 2 volume) (z : ℂ) :
    MemLp (fun w ↦ f (w - z)) 2 volume := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hf.comp_measurePreserving (measurePreserving_add_right volume (-z))

private theorem cutoff_pair_tendsto (u : ℝ → ℂ → ℂ)
    (hm : ∀ r, 0 < r → MemLp (u r) 2 volume)
    (hb : ∀ R, 1 ≤ R → ∀ w, ‖u R w‖ ≤ envelope w)
    (ht : ∀ w, Tendsto (fun R ↦ u R w) atTop (𝓝 0)) (F : H) (z : ℂ) :
    Tendsto (fun R ↦ ∫ w, F w * conj (u R (w - z))) atTop (𝓝 0) := by
  have henv : MemLp envelope 2 volume := (disk_mem 1).norm.add (kernel_mem one_pos).norm
  convert! tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
    (F := fun R w ↦ F w * conj (u R (w - z))) (f := fun _ : ℂ ↦ (0 : ℂ))
    (fun w ↦ ‖F w‖ * envelope (w - z)) ?_ ?_
    ((Lp.memLp F).norm.integrable_mul (shift_mem henv z)) ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (Lp.aestronglyMeasurable F).mul (Complex.continuous_conj.comp_aestronglyMeasurable
      (shift_mem (hm R hR) z).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    apply ae_of_all
    intro w
    simpa [norm_mul] using mul_le_mul_of_nonneg_left (hb R hR (w - z)) (norm_nonneg (F w))
  · exact .of_forall fun w ↦ by
      simpa using (tendsto_const_nhds (x := F w)).mul
        (Complex.continuous_conj.continuousAt.tendsto.comp (ht (w - z)))

private theorem disk_pair {r : ℝ} (hr : 0 < r) (z : ℂ) (F : H) :
    ∫ w, F w * conj (kernel r (w - z)) = ∫ w, (transform F) w * conj (disk r (w - z)) := by
  have hK := cutoff_pair_tendsto kernel (fun _ ↦ kernel_mem) (fun R hR w ↦ (cutoff_bounds R hR w).2)
    (fun w ↦ tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop ‖w‖] with R h using by simp [kernel, h.not_gt])) F z
  have hD := cutoff_pair_tendsto disk (fun r _ ↦ disk_mem r) (fun R hR w ↦ (cutoff_bounds R hR w).1)
    (fun w ↦ by
      have ht : Tendsto (fun R : ℝ ↦ (R ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
      refine (Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr' ?_
      filter_upwards [eventually_ge_atTop ‖w‖] with R h using by simp [disk, h]) (transform F) z
  have hi (G : H) {u : ℂ → ℂ} (h : MemLp u 2 volume) :
      Integrable (fun w ↦ G w * conj (u (w - z))) := by
    exact (Lp.memLp G).integrable_mul (shift_mem h z).star
  have he : ∀ᶠ R : ℝ in atTop,
      (∫ w, F w * conj (kernel r (w - z))) - (∫ w, F w * conj (kernel R (w - z))) =
      (∫ w, (transform F) w * conj (disk r (w - z))) -
        (∫ w, (transform F) w * conj (disk R (w - z))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simpa only [Pi.sub_apply, map_sub, mul_sub, integral_sub (hi F (kernel_mem hr))
      (hi F (kernel_mem hR)), integral_sub (hi (transform F) (disk_mem r))
      (hi (transform F) (disk_mem R))] using annulus_pair hr hR z F
  simpa using tendsto_nhds_unique ((tendsto_const_nhds.sub hK).congr' he)
    (tendsto_const_nhds.sub hD)

private theorem trunc_eq_average (f : ℂ → ℂ) (hf : MemLp f 2 volume) (z : ℂ)
    (r : ℝ) (hr : 0 < r) :
    beurlingTrunc r f z = ⨍ w in closedBall z r, transform (hf.toLp f) w := by
  let F := hf.toLp f
  let G := transform F
  let S := {w : ℂ | r < ‖w - z‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  have hk : (∫ w, F w * conj (kernel r (w - z))) =
      -(∫ w in S, f w / (z - w) ^ 2) := by
    rw [← integral_neg, ← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with w hw
    change hf.toLp f w * _ = _
    rw [hw]
    by_cases h : r < ‖w - z‖
    · have hsquare : (z - w) ^ 2 = (w - z) ^ 2 := by ring
      simp [kernel, h, S, Set.indicator, hsquare, div_eq_mul_inv]
    · simp [kernel, h, S, Set.indicator]
  have hd : (∫ w, G w * conj (disk r (w - z))) =
      ((r : ℂ) ^ 2)⁻¹ * ∫ w in closedBall z r, G w := by
    rw [← integral_const_mul, ← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards with w
    by_cases h : ‖w - z‖ ≤ r <;> simp [disk, h, Set.indicator, dist_eq_norm, mul_comm]
  have hb := disk_pair hr z F
  rw [hk, hd] at hb
  rw [beurlingTrunc, setAverage_eq]
  change -(1 / (π : ℂ)) * (∫ w in S, f w / (z - w) ^ 2) =
    _ • ∫ w in closedBall z r, G w
  rw [neg_mul, neg_mul_eq_mul_neg, hb, Measure.real, Complex.volume_closedBall,
    Complex.real_smul]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    mul_assoc, mul_comm]

/-- **The Beurling–Ahlfors transform has $L^2$ norm $1$.** For a function
$f : \mathbb{C} \to \mathbb{C}$ let $Bf(z)$ be the limit as $\varepsilon \to 0^+$ of
$-\frac{1}{\pi} \int_{|w - z| > \varepsilon} \frac{f(w)}{(z - w)^2} \, dA(w)$, where $dA$ is
Lebesgue area measure (a junk value where the limit does not exist). The infimum $\|B\|_2$ of the
constants $C \ge 0$ such that $\|Bf\|_{L^2} \le C\,\|f\|_{L^2}$ in $[0, \infty]$ for every almost
everywhere strongly measurable $f : \mathbb{C} \to \mathbb{C}$ (taken to be $0$ when there is no
such $C$) equals $1$.

Proof: By Plancherel's theorem the Fourier multiplier $\bar\xi/\xi$, of modulus one almost
everywhere, defines an isometry $T$ of $L^2$. For $f \in L^2$, the disk-average formula in the
proof of Theorem 3 of J. Mateu and J. Verdera, Math. Res. Lett. 13 (2006),
https://arxiv.org/abs/math/0603077, writes the truncated integral at radius $\varepsilon$ as the
average of $Tf$ over the closed disk of radius $\varepsilon$ about $z$. By Lebesgue's
differentiation theorem $Bf = Tf$ almost everywhere, so $\|Bf\|_{L^2} = \|f\|_{L^2}$; the
indicator of a disk shows that no constant below $1$ works.

Source: the `L²` isometry recorded in Bañuelos--Janakiraman (2008),
introduction: `‖B‖₂ = 1`. -/
public theorem l2Norm_wanted :
    beurlingNorm 2 = 1 := by
  have he (f : ℂ → ℂ) (hf : MemLp f 2 volume) :
      eLpNorm (beurlingTransform f) 2 volume = eLpNorm f 2 volume := by
    let g := transform (hf.toLp f)
    have hlim := IsUnifLocDoublingMeasure.ae_tendsto_average volume
      ((Lp.memLp g).locallyIntegrable (by norm_num)) 1
    have hfg : beurlingTransform f =ᵐ[volume] g := by
      filter_upwards [hlim] with z hz
      apply Tendsto.limUnder_eq
      refine (hz (fun _ : ℝ ↦ z) id tendsto_id ?_).congr' ?_
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mem_closedBall_self (by simpa using (le_of_lt hr))
      · filter_upwards [self_mem_nhdsWithin] with r hr using (trunc_eq_average f hf z r hr).symm
    rw [eLpNorm_congr_ae hfg, ← Lp.eNorm_def, ← Lp.eNorm_toLp hf]
    simpa only [ofReal_norm] using congrArg ENNReal.ofReal (transform_norm (hf.toLp f))
  have hu : IsBound 2 1 := by
    intro f _
    norm_num only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, one_mul]
    by_cases ht : eLpNorm f 2 volume = ⊤
    · simp [ht]
    · exact (he f (lt_top_iff_ne_top.mpr ht)).le
  refine le_antisymm (beurlingNorm_le_of_isBound zero_le_one hu) ?_
  refine le_csInf ⟨1, zero_le_one, hu⟩ ?_
  rintro C ⟨hC, h⟩
  -- Cancel the positive, finite norm of a disk indicator to prove sharpness.
  let s := ball (0 : ℂ) 1
  let f := s.indicator (fun _ ↦ (1 : ℂ))
  have hm : MemLp f 2 volume := memLp_indicator_const _
    measurableSet_ball.nullMeasurableSet _ (Or.inr measure_ball_lt_top.ne)
  have hp : 0 < (eLpNorm f 2 volume).toReal := by
    simpa [f, s, eLpNorm_indicator_const measurableSet_ball.nullMeasurableSet,
      Complex.volume_ball, ← ENNReal.toReal_rpow] using
      Real.rpow_pos_of_pos Real.pi_pos (2 : ℝ)⁻¹
  have hb := h f hm.aestronglyMeasurable
  rw [ENNReal.ofReal_ofNat, he f hm] at hb
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.eLpNorm_ne_top) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hh
  nlinarith

end
end MathlibExt.Analysis.BeurlingAhlforsWanted
