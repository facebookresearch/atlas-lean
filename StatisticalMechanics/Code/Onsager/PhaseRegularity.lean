/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Mathlib
import Code.Onsager.CriticalIntegrability

namespace StatMech.Onsager


noncomputable def ons_gIntBetaDeriv (beta k1 k2 : ℝ) : ℝ :=
  2 * Real.cosh (2 * beta) *
    (2 * Real.sinh (2 * beta) - Real.cos k1 - Real.cos k2)


noncomputable def ons_gIntBetaDeriv2 (beta k1 k2 : ℝ) : ℝ :=
  4 * Real.sinh (2 * beta) *
      (2 * Real.sinh (2 * beta) - Real.cos k1 - Real.cos k2) +
    8 * Real.cosh (2 * beta) ^ 2


noncomputable def ons_logGIntBetaDeriv (beta k1 k2 : ℝ) : ℝ :=
  ons_gIntBetaDeriv beta k1 k2 / ons_gInt beta k1 k2


noncomputable def ons_logGIntBetaDeriv2 (beta k1 k2 : ℝ) : ℝ :=
  (ons_gIntBetaDeriv2 beta k1 k2 * ons_gInt beta k1 k2 -
      ons_gIntBetaDeriv beta k1 k2 ^ 2) /
    ons_gInt beta k1 k2 ^ 2

theorem ons_hasDerivAt_gInt (beta k1 k2 : ℝ) :
    HasDerivAt (fun b => ons_gInt b k1 k2)
      (ons_gIntBetaDeriv beta k1 k2) beta := by
  have hlin : HasDerivAt (fun b : ℝ => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1
    all_goals ring
  have hcosh : HasDerivAt (fun b : ℝ => Real.cosh (2 * b))
      (2 * Real.sinh (2 * beta)) beta := by
    convert (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hsinh : HasDerivAt (fun b : ℝ => Real.sinh (2 * b))
      (2 * Real.cosh (2 * beta)) beta := by
    convert (Real.hasDerivAt_sinh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hprod := hsinh.const_mul (Real.cos k1 + Real.cos k2)
  have h := (hcosh.pow 2).sub hprod
  convert h using 1
  · ext b
    simp only [ons_gInt, Pi.pow_apply, Pi.sub_apply]
    ring
  · simp only [ons_gIntBetaDeriv]
    ring

theorem ons_hasDerivAt_gIntBetaDeriv (beta k1 k2 : ℝ) :
    HasDerivAt (fun b => ons_gIntBetaDeriv b k1 k2)
      (ons_gIntBetaDeriv2 beta k1 k2) beta := by
  have hlin : HasDerivAt (fun b : ℝ => 2 * b) 2 beta := by
    convert (hasDerivAt_id beta).const_mul 2 using 1
    all_goals ring
  have hcosh : HasDerivAt (fun b : ℝ => Real.cosh (2 * b))
      (2 * Real.sinh (2 * beta)) beta := by
    convert (Real.hasDerivAt_cosh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hsinh : HasDerivAt (fun b : ℝ => Real.sinh (2 * b))
      (2 * Real.cosh (2 * beta)) beta := by
    convert (Real.hasDerivAt_sinh (2 * beta)).comp beta hlin using 1
    all_goals ring
  have hinner : HasDerivAt
      (fun b : ℝ => 2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2)
      (4 * Real.cosh (2 * beta)) beta := by
    convert (hsinh.const_mul 2).sub_const (Real.cos k1) |>.sub_const (Real.cos k2)
      using 1
    all_goals ring
  have h := (hcosh.const_mul 2).mul hinner
  convert h using 1
  all_goals simp only [ons_gIntBetaDeriv2]
  all_goals ring

theorem ons_hasDerivAt_log_gInt (beta k1 k2 : ℝ)
    (hne : ons_gInt beta k1 k2 ≠ 0) :
    HasDerivAt (fun b => Real.log (ons_gInt b k1 k2))
      (ons_logGIntBetaDeriv beta k1 k2) beta := by
  simpa only [ons_logGIntBetaDeriv] using
    (ons_hasDerivAt_gInt beta k1 k2).log hne

theorem ons_hasDerivAt_logGIntBetaDeriv (beta k1 k2 : ℝ)
    (hne : ons_gInt beta k1 k2 ≠ 0) :
    HasDerivAt (fun b => ons_logGIntBetaDeriv b k1 k2)
      (ons_logGIntBetaDeriv2 beta k1 k2) beta := by
  unfold ons_logGIntBetaDeriv ons_logGIntBetaDeriv2
  convert (ons_hasDerivAt_gIntBetaDeriv beta k1 k2).div
    (ons_hasDerivAt_gInt beta k1 k2) hne using 1
  all_goals simp [pow_two]

theorem ons_cosh_betaC_sq : Real.cosh (2 * ons_betaC) ^ 2 = 2 := by
  have h := Real.cosh_sq_sub_sinh_sq (2 * ons_betaC)
  rw [ons_betaC_sinh] at h
  nlinarith

theorem ons_gIntBetaDeriv_betaC (k1 k2 : ℝ) :
    ons_gIntBetaDeriv ons_betaC k1 k2 =
      2 * Real.cosh (2 * ons_betaC) * (2 - Real.cos k1 - Real.cos k2) := by
  simp only [ons_gIntBetaDeriv, ons_betaC_sinh]
  ring

theorem ons_gIntBetaDeriv2_betaC (k1 k2 : ℝ) :
    ons_gIntBetaDeriv2 ons_betaC k1 k2 =
      4 * (2 - Real.cos k1 - Real.cos k2) + 16 := by
  rw [ons_gIntBetaDeriv2, ons_betaC_sinh, ons_cosh_betaC_sq]
  ring



theorem ons_logGIntBetaDeriv_betaC (k1 k2 : ℝ)
    (hne : 2 - Real.cos k1 - Real.cos k2 ≠ 0) :
    ons_logGIntBetaDeriv ons_betaC k1 k2 = 2 * Real.cosh (2 * ons_betaC) := by
  rw [ons_logGIntBetaDeriv, ons_gIntBetaDeriv_betaC, ons_gInt_betaC]
  field_simp




theorem ons_logGIntBetaDeriv2_betaC (k1 k2 : ℝ)
    (hne : 2 - Real.cos k1 - Real.cos k2 ≠ 0) :
    ons_logGIntBetaDeriv2 ons_betaC k1 k2 =
      -4 + 16 / (2 - Real.cos k1 - Real.cos k2) := by
  rw [ons_logGIntBetaDeriv2, ons_gIntBetaDeriv2_betaC,
    ons_gIntBetaDeriv_betaC, ons_gInt_betaC]
  have hc := ons_cosh_betaC_sq
  field_simp [hne]
  rw [hc]
  ring


theorem ons_criticalDenom_le_sq (x y : ℝ) :
    2 - Real.cos x - Real.cos y ≤ (x ^ 2 + y ^ 2) / 2 := by
  have hx := Real.one_sub_sq_div_two_le_cos (x := x)
  have hy := Real.one_sub_sq_div_two_le_cos (x := y)
  linarith



theorem ons_criticalDenom_pos {x y : ℝ} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    0 < 2 - Real.cos x - Real.cos y := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcosx : Real.cos x < 1 := by
    have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, hpi.le⟩)
      (show x ∈ Set.Icc 0 Real.pi by exact ⟨hx.le, hxpi⟩) hx
    simpa using h
  have hcosy : Real.cos y ≤ 1 := Real.cos_le_one y
  linarith




theorem ons_criticalKernel_lower_on_wedge {x y : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) (hxy : x ≤ y) (hy2x : y ≤ 2 * x) :
    2 / (5 * x ^ 2) ≤ 1 / (2 - Real.cos x - Real.cos y) := by
  have hxpi : x ≤ Real.pi := by linarith
  have hden : 0 < 2 - Real.cos x - Real.cos y :=
    ons_criticalDenom_pos hx hxpi
  have hySq : y ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  have hupper : 2 - Real.cos x - Real.cos y ≤ (5 / 2 : ℝ) * x ^ 2 := by
    have hquad := ons_criticalDenom_le_sq x y
    nlinarith
  have hinv := one_div_le_one_div_of_le hden hupper
  convert hinv using 1
  field_simp



theorem ons_criticalKernel_innerIntegral_lower {x : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) :
    2 / (5 * x) ≤
      ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y) := by
  have hx2x : x ≤ 2 * x := by linarith
  have hxpi : x ≤ Real.pi := by linarith
  have hkernelCont : ContinuousOn
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y)) (Set.uIcc x (2 * x)) := by
    have hdenCont : Continuous (fun y : ℝ => 2 - Real.cos x - Real.cos y) :=
      (show Continuous (fun y : ℝ => (2 - Real.cos x) - Real.cos y) from
        continuous_const.sub Real.continuous_cos)
    apply ContinuousOn.div continuousOn_const hdenCont.continuousOn
    intro y _hy
    exact (ons_criticalDenom_pos hx hxpi).ne'
  have hconstInt : IntervalIntegrable (fun _y : ℝ => 2 / (5 * x ^ 2))
      MeasureTheory.volume x (2 * x) :=
    continuousOn_const.intervalIntegrable
  have hkernelInt : IntervalIntegrable
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y))
      MeasureTheory.volume x (2 * x) :=
    hkernelCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx2x hconstInt hkernelInt
    (fun y hy => ons_criticalKernel_lower_on_wedge hx h2xpi hy.1 hy.2)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  convert hmono using 1
  field_simp
  ring


theorem ons_logKernel_integral {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta) :
    (∫ x in epsilon..delta, 2 / (5 * x)) =
      (2 / 5 : ℝ) * Real.log (delta / epsilon) := by
  have hzero : 0 ∉ Set.uIcc epsilon delta := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with h | h
    · linarith
    · linarith
  calc
    (∫ x in epsilon..delta, 2 / (5 * x)) =
        ∫ x in epsilon..delta, (2 / 5 : ℝ) * x⁻¹ := by
          apply intervalIntegral.integral_congr
          intro x _hx
          field_simp
    _ = (2 / 5 : ℝ) * ∫ x in epsilon..delta, x⁻¹ :=
      intervalIntegral.integral_const_mul _ _
    _ = (2 / 5 : ℝ) * Real.log (delta / epsilon) := by
      rw [integral_inv hzero]



theorem ons_logKernel_cutoff_tendsto (delta : ℝ) (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun n : ℕ => (2 / 5 : ℝ) *
        Real.log (delta / Real.exp (-(n : ℝ))))
      Filter.atTop Filter.atTop := by
  have hbase : Filter.Tendsto (fun n : ℕ => Real.log delta + (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hmul := hbase.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 5)
  convert hmul using 1
  funext n
  rw [Real.log_div hdelta.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring






noncomputable def ons_criticalKernelClamp (epsilon x y : ℝ) : ℝ :=
  1 / max (2 - Real.cos x - Real.cos y) (1 - Real.cos epsilon)

theorem ons_one_sub_cos_pos {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonPi : epsilon ≤ Real.pi) :
    0 < 1 - Real.cos epsilon := by
  have h := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show epsilon ∈ Set.Icc 0 Real.pi by exact ⟨hepsilon.le, hepsilonPi⟩)
    hepsilon
  simpa using h

theorem ons_criticalKernelClamp_continuous (epsilon : ℝ)
    (hcut : 0 < 1 - Real.cos epsilon) :
    Continuous (Function.uncurry (ons_criticalKernelClamp epsilon)) := by
  have hden : Continuous
      (fun p : ℝ × ℝ => 2 - Real.cos p.1 - Real.cos p.2) :=
    (continuous_const.sub (Real.continuous_cos.comp continuous_fst)).sub
      (Real.continuous_cos.comp continuous_snd)
  have hmax : Continuous
      (fun p : ℝ × ℝ =>
        max (2 - Real.cos p.1 - Real.cos p.2) (1 - Real.cos epsilon)) :=
    hden.max continuous_const
  apply Continuous.div continuous_const hmax
  intro p
  exact ne_of_gt (hcut.trans_le (le_max_right _ _))

theorem ons_criticalKernelClamp_eq {epsilon delta x y : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdeltaPi : delta ≤ Real.pi)
    (hx : x ∈ Set.Icc epsilon delta) :
    ons_criticalKernelClamp epsilon x y =
      1 / (2 - Real.cos x - Real.cos y) := by
  have hepsilonPi : epsilon ≤ Real.pi := hx.1.trans (hx.2.trans hdeltaPi)
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  have hcos : Real.cos x ≤ Real.cos epsilon :=
    Real.antitoneOn_cos ⟨hepsilon, hepsilonPi⟩ ⟨hepsilon.trans hx.1, hxPi⟩ hx.1
  have hcosy := Real.cos_le_one y
  have hle : 1 - Real.cos epsilon ≤ 2 - Real.cos x - Real.cos y := by
    linarith
  rw [ons_criticalKernelClamp, max_eq_left hle]



theorem ons_wedgeIntegral_continuous {F : ℝ → ℝ → ℝ}
    (hjoint : Continuous (Function.uncurry F)) :
    Continuous (fun x : ℝ => ∫ y in x..(2 * x), F x y) := by
  have hupper : Continuous (fun x : ℝ => 2 * x) :=
    continuous_const.mul continuous_id
  have htoUpper : Continuous (fun x : ℝ =>
      ∫ y in 0..(2 * x), F x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hjoint hupper
  have htoLower : Continuous (fun x : ℝ =>
      ∫ y in 0..x, F x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hjoint continuous_id
  have heq : (fun x : ℝ => ∫ y in x..(2 * x), F x y) =
      (fun x : ℝ =>
        (∫ y in 0..(2 * x), F x y) - ∫ y in 0..x, F x y) := by
    funext x
    symm
    apply intervalIntegral.integral_interval_sub_left
    · exact (hjoint.uncurry_left x).continuousOn.intervalIntegrable
    · exact (hjoint.uncurry_left x).continuousOn.intervalIntegrable
  rw [heq]
  exact htoUpper.sub htoLower

theorem ons_criticalKernelClamp_inner_continuous (epsilon : ℝ)
    (hcut : 0 < 1 - Real.cos epsilon) :
    Continuous (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_criticalKernelClamp epsilon x y) :=
  ons_wedgeIntegral_continuous (ons_criticalKernelClamp_continuous epsilon hcut)

theorem ons_criticalKernel_inner_continuousOn {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y))
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  apply (ons_criticalKernelClamp_inner_continuous epsilon hcut).continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  exact (ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx).symm


theorem ons_criticalKernel_wedgeIntegral_lower {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (h2deltaPi : 2 * delta ≤ Real.pi) :
    (2 / 5 : ℝ) * Real.log (delta / epsilon) ≤
      ∫ x in epsilon..delta,
        ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y) := by
  have hdeltaPi : delta ≤ Real.pi := by linarith
  have hinnerInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y))
      MeasureTheory.volume epsilon delta := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hed] using
      ons_criticalKernel_inner_continuousOn hepsilon hed hdeltaPi
  have hcompCont : ContinuousOn (fun x : ℝ => 2 / (5 * x))
      (Set.uIcc epsilon delta) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.mul continuousOn_id)
    intro x hx
    rw [Set.mem_uIcc] at hx
    intro hzero
    change 5 * x = 0 at hzero
    rcases hx with hx | hx <;> nlinarith
  have hcompInt : IntervalIntegrable (fun x : ℝ => 2 / (5 * x))
      MeasureTheory.volume epsilon delta :=
    hcompCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hed hcompInt hinnerInt
    (fun x hx => ons_criticalKernel_innerIntegral_lower
      (hepsilon.trans_le hx.1) (by nlinarith [hx.2]))
  rw [ons_logKernel_integral hepsilon hed] at hmono
  exact hmono




theorem ons_criticalKernel_wedgeCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..1,
          ∫ y in x..(2 * x), 1 / (2 - Real.cos x - Real.cos y))
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun n => ?_)
    (ons_logKernel_cutoff_tendsto 1 zero_lt_one)
  apply ons_criticalKernel_wedgeIntegral_lower (Real.exp_pos _)
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  · linarith [Real.pi_gt_three]



theorem ons_criticalSecondKernel_lower_on_wedge {x y : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) (hxy : x ≤ y) (hy2x : y ≤ 2 * x) :
    -4 + 32 / (5 * x ^ 2) ≤
      ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hxpi : x ≤ Real.pi := by linarith
  have hden : 2 - Real.cos x - Real.cos y ≠ 0 :=
    (ons_criticalDenom_pos hx hxpi).ne'
  rw [ons_logGIntBetaDeriv2_betaC x y hden]
  have hkernel := ons_criticalKernel_lower_on_wedge hx h2xpi hxy hy2x
  have hscaled := mul_le_mul_of_nonneg_left hkernel (by norm_num : (0 : ℝ) ≤ 16)
  calc
    -4 + 32 / (5 * x ^ 2) = -4 + 16 * (2 / (5 * x ^ 2)) := by ring
    _ ≤ -4 + 16 * (1 / (2 - Real.cos x - Real.cos y)) :=
      by simpa [add_comm] using add_le_add_left hscaled (-4)
    _ = -4 + 16 / (2 - Real.cos x - Real.cos y) := by ring

theorem ons_criticalSecondKernel_innerIntegral_lower {x : ℝ}
    (hx : 0 < x) (h2xpi : 2 * x ≤ Real.pi) :
    -4 * x + 32 / (5 * x) ≤
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hx2x : x ≤ 2 * x := by linarith
  have hxpi : x ≤ Real.pi := by linarith
  have hdenCont : Continuous (fun y : ℝ => 2 - Real.cos x - Real.cos y) :=
    (show Continuous (fun y : ℝ => (2 - Real.cos x) - Real.cos y) from
      continuous_const.sub Real.continuous_cos)
  have hkernelCont : ContinuousOn
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y)) (Set.uIcc x (2 * x)) := by
    apply ContinuousOn.div continuousOn_const hdenCont.continuousOn
    intro y _hy
    exact (ons_criticalDenom_pos hx hxpi).ne'
  have hsecondCont : ContinuousOn
      (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y) (Set.uIcc x (2 * x)) := by
    have hexpr : ContinuousOn
        (fun y : ℝ => -4 + 16 * (1 / (2 - Real.cos x - Real.cos y)))
        (Set.uIcc x (2 * x)) :=
      continuousOn_const.add (continuousOn_const.mul hkernelCont)
    apply hexpr.congr
    intro y _hy
    change ons_logGIntBetaDeriv2 ons_betaC x y =
      -4 + 16 * (1 / (2 - Real.cos x - Real.cos y))
    rw [ons_logGIntBetaDeriv2_betaC x y
      (ons_criticalDenom_pos hx hxpi).ne']
    ring
  have hcompInt : IntervalIntegrable (fun _y : ℝ => -4 + 32 / (5 * x ^ 2))
      MeasureTheory.volume x (2 * x) :=
    continuousOn_const.intervalIntegrable
  have hsecondInt : IntervalIntegrable
      (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume x (2 * x) :=
    hsecondCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx2x hcompInt hsecondInt
    (fun y hy => ons_criticalSecondKernel_lower_on_wedge hx h2xpi hy.1 hy.2)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  convert hmono using 1
  field_simp
  ring

noncomputable def ons_criticalSecondKernelClamp (epsilon x y : ℝ) : ℝ :=
  -4 + 16 * ons_criticalKernelClamp epsilon x y

theorem ons_criticalSecondKernelClamp_continuous (epsilon : ℝ)
    (hcut : 0 < 1 - Real.cos epsilon) :
    Continuous (Function.uncurry (ons_criticalSecondKernelClamp epsilon)) := by
  have hk := ons_criticalKernelClamp_continuous epsilon hcut
  exact continuous_const.add (continuous_const.mul hk)

theorem ons_criticalSecondKernel_inner_continuousOn {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  have hclamp := ons_wedgeIntegral_continuous
    (ons_criticalSecondKernelClamp_continuous epsilon hcut)
  apply hclamp.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  rw [ons_criticalSecondKernelClamp,
    ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx,
    ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos
      (hepsilon.trans_le hx.1) hxPi).ne']
  ring

theorem ons_criticalSecondComparison_integral {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) :
    (∫ x in epsilon..1, (-4 + 32 / (5 * x))) =
      -4 * (1 - epsilon) + (32 / 5 : ℝ) * Real.log (1 / epsilon) := by
  have hconst : IntervalIntegrable (fun _x : ℝ => (-4 : ℝ))
      MeasureTheory.volume epsilon 1 := continuousOn_const.intervalIntegrable
  have hlog : IntervalIntegrable (fun x : ℝ => 32 / (5 * x))
      MeasureTheory.volume epsilon 1 := by
    have hcont : ContinuousOn (fun x : ℝ => 32 / (5 * x))
        (Set.uIcc epsilon 1) := by
      apply ContinuousOn.div continuousOn_const
        (continuousOn_const.mul continuousOn_id)
      intro x hx hzero
      change 5 * x = 0 at hzero
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx <;> nlinarith
    exact hcont.intervalIntegrable
  rw [intervalIntegral.integral_add hconst hlog, intervalIntegral.integral_const]
  norm_num only [smul_eq_mul]
  have hscale : (∫ x in epsilon..1, 32 / (5 * x)) =
      16 * ∫ x in epsilon..1, 2 / (5 * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hscale, ons_logKernel_integral hepsilon hepsilonOne]
  ring

theorem ons_criticalSecond_wedgeCutoff_lower (n : ℕ) :
    -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..1,
        ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  change -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonOne : epsilon ≤ 1 := by
    change Real.exp (-(n : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have hdeltaPi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hinnerInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecondKernel_inner_continuousOn hepsilon hepsilonOne hdeltaPi
  have hcompCont : ContinuousOn (fun x : ℝ => -4 + 32 / (5 * x))
      (Set.uIcc epsilon 1) := by
    apply continuousOn_const.add
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.mul continuousOn_id)
    intro x hx hzero
    change 5 * x = 0 at hzero
    rw [Set.mem_uIcc] at hx
    rcases hx with hx | hx <;> nlinarith
  have hcompInt : IntervalIntegrable (fun x : ℝ => -4 + 32 / (5 * x))
      MeasureTheory.volume epsilon 1 := hcompCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hepsilonOne hcompInt hinnerInt
    (fun x hx => by
      rcases hx with ⟨hxlo, hxhi⟩
      have hinner := ons_criticalSecondKernel_innerIntegral_lower
        (hepsilon.trans_le hxlo) (by linarith [hxhi, Real.pi_gt_three])
      nlinarith)
  rw [ons_criticalSecondComparison_integral hepsilon hepsilonOne] at hmono
  have hlog : Real.log (1 / epsilon) = (n : ℝ) := by
    rw [show epsilon = Real.exp (-(n : ℝ)) by rfl,
      Real.log_div one_ne_zero (Real.exp_ne_zero _), Real.log_one,
      Real.log_exp]
    ring
  rw [hlog] at hmono
  nlinarith




theorem ons_criticalSecond_wedgeCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..1,
          ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono ons_criticalSecond_wedgeCutoff_lower
  have hbase : Filter.Tendsto (fun n : ℕ => (32 / 5 : ℝ) * (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.add_atTop hbase

theorem ons_criticalSecondKernel_ge_neg_four {x y : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    -4 ≤ ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hdenPos := ons_criticalDenom_pos (y := y) hx hxpi
  rw [ons_logGIntBetaDeriv2_betaC x y hdenPos.ne']
  have hnonneg : 0 ≤ 16 / (2 - Real.cos x - Real.cos y) :=
    div_nonneg (by norm_num) hdenPos.le
  linarith

theorem ons_criticalSecondKernel_intervalIntegrable {x a b : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    IntervalIntegrable (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume a b := by
  have hdenCont : Continuous (fun y : ℝ => 2 - Real.cos x - Real.cos y) :=
    (show Continuous (fun y : ℝ => (2 - Real.cos x) - Real.cos y) from
      continuous_const.sub Real.continuous_cos)
  have hkernelCont : Continuous
      (fun y : ℝ => 1 / (2 - Real.cos x - Real.cos y)) := by
    apply Continuous.div continuous_const hdenCont
    intro y
    exact (ons_criticalDenom_pos hx hxpi).ne'
  have hexpr : Continuous
      (fun y : ℝ => -4 + 16 * (1 / (2 - Real.cos x - Real.cos y))) :=
    continuous_const.add (continuous_const.mul hkernelCont)
  have hsecond : Continuous
      (fun y : ℝ => ons_logGIntBetaDeriv2 ons_betaC x y) := by
    apply hexpr.congr
    intro y
    change -4 + 16 * (1 / (2 - Real.cos x - Real.cos y)) =
      ons_logGIntBetaDeriv2 ons_betaC x y
    rw [ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos hx hxpi).ne']
    ring
  exact hsecond.continuousOn.intervalIntegrable

theorem ons_criticalSecondKernel_interval_lower {x a b : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) (hab : a ≤ b) :
    -4 * (b - a) ≤
      ∫ y in a..b, ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hconst : IntervalIntegrable (fun _y : ℝ => (-4 : ℝ))
      MeasureTheory.volume a b := continuousOn_const.intervalIntegrable
  have hsecond := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := a) (b := b)
  have hmono := intervalIntegral.integral_mono_on hab hconst hsecond
    (fun y _hy => ons_criticalSecondKernel_ge_neg_four hx hxpi)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  simpa [mul_comm] using hmono



theorem ons_criticalSecondKernel_rectInner_lower {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) :
    (∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) - 8 ≤
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hxpi : x ≤ Real.pi := hxone.trans (by linarith [Real.pi_gt_three])
  have h0x := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := 0) (b := x)
  have hxx2 := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := x) (b := 2 * x)
  have hx22 := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := 2 * x) (b := 2)
  have hlower0 := ons_criticalSecondKernel_interval_lower hx hxpi (show 0 ≤ x from hx.le)
  have hlower2 := ons_criticalSecondKernel_interval_lower hx hxpi
    (show 2 * x ≤ 2 by linarith)
  have hjoin1 := intervalIntegral.integral_add_adjacent_intervals h0x hxx2
  have hjoin2 := intervalIntegral.integral_add_adjacent_intervals
    (h0x.trans hxx2) hx22
  linarith

theorem ons_criticalSecond_rectInner_continuousOn {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  have hjoint := ons_criticalSecondKernelClamp_continuous epsilon hcut
  have hclamp : Continuous (fun x : ℝ =>
      ∫ y in 0..2, ons_criticalSecondKernelClamp epsilon x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint 0 2
  apply hclamp.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  rw [ons_criticalSecondKernelClamp,
    ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx,
    ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos
      (hepsilon.trans_le hx.1) hxPi).ne']
  ring

theorem ons_criticalSecond_fixedInner_continuousOn {epsilon delta a b : ℝ}
    (hepsilon : 0 < epsilon) (hed : epsilon ≤ delta)
    (hdeltaPi : delta ≤ Real.pi) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in a..b, ons_logGIntBetaDeriv2 ons_betaC x y)
      (Set.Icc epsilon delta) := by
  have hepsilonPi : epsilon ≤ Real.pi := hed.trans hdeltaPi
  have hcut := ons_one_sub_cos_pos hepsilon hepsilonPi
  have hjoint := ons_criticalSecondKernelClamp_continuous epsilon hcut
  have hclamp : Continuous (fun x : ℝ =>
      ∫ y in a..b, ons_criticalSecondKernelClamp epsilon x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hjoint a b
  apply hclamp.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y _hy
  have hxPi : x ≤ Real.pi := hx.2.trans hdeltaPi
  rw [ons_criticalSecondKernelClamp,
    ons_criticalKernelClamp_eq hepsilon.le hdeltaPi hx,
    ons_logGIntBetaDeriv2_betaC x y (ons_criticalDenom_pos
      (hepsilon.trans_le hx.1) hxPi).ne']
  ring

theorem ons_criticalSecond_rectCutoff_lower (n : ℕ) :
    -12 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..1,
        ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  change -12 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonOne : epsilon ≤ 1 := by
    change Real.exp (-(n : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hwedgeInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecondKernel_inner_continuousOn hepsilon hepsilonOne hpi
  have hleftInt : IntervalIntegrable (fun x : ℝ =>
      (∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y) - 8)
      MeasureTheory.volume epsilon 1 :=
    hwedgeInt.sub (continuousOn_const.intervalIntegrable)
  have hrectInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecond_rectInner_continuousOn hepsilon hepsilonOne hpi
  have hmono := intervalIntegral.integral_mono_on hepsilonOne hleftInt hrectInt
    (fun x hx => ons_criticalSecondKernel_rectInner_lower
      (hepsilon.trans_le hx.1) hx.2)
  rw [intervalIntegral.integral_sub hwedgeInt
    (continuousOn_const.intervalIntegrable), intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  have hwedge := ons_criticalSecond_wedgeCutoff_lower n
  change -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in x..(2 * x), ons_logGIntBetaDeriv2 ons_betaC x y at hwedge
  nlinarith



theorem ons_criticalSecond_rectCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..1,
          ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono ons_criticalSecond_rectCutoff_lower
  have hbase : Filter.Tendsto (fun n : ℕ => (32 / 5 : ℝ) * (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.add_atTop hbase

theorem ons_criticalSecond_positiveInner_rect_lower {x : ℝ}
    (hx : 0 < x) (hxone : x ≤ 1) :
    (∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi ≤
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
  have hxpi : x ≤ Real.pi := hxone.trans (by linarith [Real.pi_gt_three])
  have h02 := ons_criticalSecondKernel_intervalIntegrable hx hxpi (a := 0) (b := 2)
  have h2pi := ons_criticalSecondKernel_intervalIntegrable hx hxpi
    (a := 2) (b := Real.pi)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals h02 h2pi
  have hlower := ons_criticalSecondKernel_interval_lower hx hxpi
    (show (2 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
  linarith [Real.pi_pos]

theorem ons_criticalSecond_positiveQuadrantCutoff_lower (n : ℕ) :
    -12 - 4 * Real.pi ^ 2 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..Real.pi,
        ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  change -12 - 4 * Real.pi ^ 2 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..Real.pi,
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonOne : epsilon ≤ 1 := by
    change Real.exp (-(n : ℝ)) ≤ 1
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have honePi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hrectInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecond_rectInner_continuousOn hepsilon hepsilonOne honePi
  have hpositiveInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hepsilonOne] using
      ons_criticalSecond_fixedInner_continuousOn
        (a := 0) (b := Real.pi) hepsilon hepsilonOne honePi
  have hleftInt : IntervalIntegrable (fun x : ℝ =>
      (∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi)
      MeasureTheory.volume epsilon 1 :=
    hrectInt.sub continuousOn_const.intervalIntegrable
  have hfirstMono := intervalIntegral.integral_mono_on hepsilonOne hleftInt hpositiveInt
    (fun x hx => ons_criticalSecond_positiveInner_rect_lower
      (hepsilon.trans_le hx.1) hx.2)
  rw [intervalIntegral.integral_sub hrectInt continuousOn_const.intervalIntegrable,
    intervalIntegral.integral_const] at hfirstMono
  norm_num only [smul_eq_mul] at hfirstMono
  have hfirst :
      (∫ x in epsilon..1,
        ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y) - 4 * Real.pi ≤
      ∫ x in epsilon..1,
        ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
    have hepsNonneg := hepsilon.le
    nlinarith [Real.pi_pos]
  have htailInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume 1 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le honePi] using
      ons_criticalSecond_fixedInner_continuousOn
        (epsilon := 1) (delta := Real.pi) (a := 0) (b := Real.pi)
        zero_lt_one honePi le_rfl
  have htailPoint : ∀ x ∈ Set.Icc (1 : ℝ) Real.pi,
      -4 * Real.pi ≤
        ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y := by
    intro x hx
    simpa using ons_criticalSecondKernel_interval_lower (zero_lt_one.trans_le hx.1)
      hx.2 Real.pi_pos.le
  have htailConst : IntervalIntegrable (fun _x : ℝ => -4 * Real.pi)
      MeasureTheory.volume 1 Real.pi := continuousOn_const.intervalIntegrable
  have htailMono := intervalIntegral.integral_mono_on honePi htailConst htailInt htailPoint
  rw [intervalIntegral.integral_const] at htailMono
  norm_num only [smul_eq_mul] at htailMono
  have hwholeInt : IntervalIntegrable (fun x : ℝ =>
      ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      MeasureTheory.volume epsilon Real.pi := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (hepsilonOne.trans honePi)] using
      ons_criticalSecond_fixedInner_continuousOn
        (a := 0) (b := Real.pi) hepsilon (hepsilonOne.trans honePi) le_rfl
  have hjoin := intervalIntegral.integral_add_adjacent_intervals hpositiveInt htailInt
  have hrect := ons_criticalSecond_rectCutoff_lower n
  change -12 + (32 / 5 : ℝ) * (n : ℝ) ≤
    ∫ x in epsilon..1,
      ∫ y in 0..2, ons_logGIntBetaDeriv2 ons_betaC x y at hrect
  nlinarith [Real.pi_pos, sq_nonneg (Real.pi - 1)]



theorem ons_criticalSecond_positiveQuadrantCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in Real.exp (-(n : ℝ))..Real.pi,
          ∫ y in 0..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono ons_criticalSecond_positiveQuadrantCutoff_lower
  have hbase : Filter.Tendsto (fun n : ℕ => (32 / 5 : ℝ) * (n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  exact tendsto_const_nhds.add_atTop hbase

theorem ons_logGIntBetaDeriv2_neg_left (beta x y : ℝ) :
    ons_logGIntBetaDeriv2 beta (-x) y = ons_logGIntBetaDeriv2 beta x y := by
  simp [ons_logGIntBetaDeriv2, ons_gIntBetaDeriv2, ons_gIntBetaDeriv,
    ons_gInt, Real.cos_neg]

theorem ons_logGIntBetaDeriv2_neg_right (beta x y : ℝ) :
    ons_logGIntBetaDeriv2 beta x (-y) = ons_logGIntBetaDeriv2 beta x y := by
  simp [ons_logGIntBetaDeriv2, ons_gIntBetaDeriv2, ons_gIntBetaDeriv,
    ons_gInt, Real.cos_neg]

theorem ons_criticalSecond_inner_full_eq_two {x : ℝ}
    (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv2 ons_betaC x y) =
      2 * ∫ y in 0..Real.pi,
        ons_logGIntBetaDeriv2 ons_betaC x y := by
  let f : ℝ → ℝ := fun y => ons_logGIntBetaDeriv2 ons_betaC x y
  have hneg : (∫ y in (-Real.pi)..0, f y) = ∫ y in 0..Real.pi, f y := by
    have hchange := intervalIntegral.integral_comp_neg (a := 0) (b := Real.pi) f
    have heven : (∫ y in 0..Real.pi, f (-y)) = ∫ y in 0..Real.pi, f y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact ons_logGIntBetaDeriv2_neg_right ons_betaC x y
    simpa only [neg_zero] using hchange.symm.trans heven
  have hleft := ons_criticalSecondKernel_intervalIntegrable hx hxpi
    (a := -Real.pi) (b := 0)
  have hright := ons_criticalSecondKernel_intervalIntegrable hx hxpi
    (a := 0) (b := Real.pi)
  have hjoin := intervalIntegral.integral_add_adjacent_intervals hleft hright
  change (∫ y in (-Real.pi)..Real.pi, f y) = 2 * ∫ y in 0..Real.pi, f y
  linarith

theorem ons_criticalSecond_fullCutoff_eq_four (n : ℕ) :
    ((∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))),
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y) +
      ∫ x in Real.exp (-(n : ℝ))..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y) =
      4 * ∫ x in Real.exp (-(n : ℝ))..Real.pi,
        ∫ y in 0..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y := by
  let epsilon := Real.exp (-(n : ℝ))
  have hepsilon : 0 < epsilon := Real.exp_pos _
  have hepsilonPi : epsilon ≤ Real.pi := by
    have hepsilonOne : epsilon ≤ 1 := by
      change Real.exp (-(n : ℝ)) ≤ 1
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (Nat.cast_nonneg n)
    linarith [Real.pi_gt_three]
  let F : ℝ → ℝ := fun x =>
    ∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv2 ons_betaC x y
  have hF_even (x : ℝ) : F (-x) = F x := by
    apply intervalIntegral.integral_congr
    intro y _hy
    exact ons_logGIntBetaDeriv2_neg_left ons_betaC x y
  have hneg : (∫ x in (-Real.pi)..(-epsilon), F x) =
      ∫ x in epsilon..Real.pi, F x := by
    have hchange := intervalIntegral.integral_comp_neg (a := epsilon) (b := Real.pi) F
    have heven : (∫ x in epsilon..Real.pi, F (-x)) = ∫ x in epsilon..Real.pi, F x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hF_even x
    linarith
  have hpos : (∫ x in epsilon..Real.pi, F x) =
      2 * ∫ x in epsilon..Real.pi,
        ∫ y in 0..Real.pi,
          ons_logGIntBetaDeriv2 ons_betaC x y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hepsilonPi] at hx
    exact ons_criticalSecond_inner_full_eq_two
      (hepsilon.trans_le hx.1) hx.2
  change (∫ x in (-Real.pi)..(-epsilon), F x) +
      (∫ x in epsilon..Real.pi, F x) = _
  rw [hneg, hpos]
  ring





theorem ons_criticalSecond_fullCutoff_tendsto :
    Filter.Tendsto
      (fun n : ℕ =>
        (∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))),
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y) +
          ∫ x in Real.exp (-(n : ℝ))..Real.pi,
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  have hscale := ons_criticalSecond_positiveQuadrantCutoff_tendsto.const_mul_atTop
    (by norm_num : (0 : ℝ) < 4)
  apply hscale.congr'
  exact Filter.Eventually.of_forall fun n =>
    (ons_criticalSecond_fullCutoff_eq_four n).symm



theorem ons_cos_lt_one_of_mem_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hne : x ≠ 0) :
    Real.cos x < 1 := by
  rcases hx with ⟨hxl, hxu⟩
  have hperiod := Real.cos_eq_one_iff_of_lt_of_lt
    (show -(2 * Real.pi) < x by linarith [Real.pi_pos])
    (show x < 2 * Real.pi by linarith [Real.pi_pos])
  have hcosne : Real.cos x ≠ 1 := by
    intro hcos
    exact hne (hperiod.mp hcos)
  exact lt_of_le_of_ne (Real.cos_le_one x) hcosne

theorem ons_criticalDenom_pos_of_mem_Icc_left {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hne : x ≠ 0) :
    0 < 2 - Real.cos x - Real.cos y := by
  have hxcos := ons_cos_lt_one_of_mem_Icc hx hne
  have hycos := Real.cos_le_one y
  linarith

theorem ons_criticalFirst_inner_integral (x : ℝ)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv ons_betaC x y) =
      (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)) := by
  let c : ℝ := 2 * Real.cosh (2 * ons_betaC)
  have hconst : (∫ _y in (-Real.pi)..Real.pi, c) = (2 * Real.pi) * c := by
    rw [intervalIntegral.integral_const]
    norm_num only [smul_eq_mul]
    ring
  by_cases hx0 : x = 0
  · subst x
    have hyne : ∀ᵐ y : ℝ ∂MeasureTheory.volume, y ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have hset : {y : ℝ | ¬y ≠ 0} = ({0} : Set ℝ) := by
        ext y
        simp
      rw [hset]
      exact MeasureTheory.measure_singleton 0
    have heq : (∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC 0 y) =
        ∫ _y in (-Real.pi)..Real.pi, c := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hyne] with y hy0 hyI
      have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
        rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
        exact ⟨hyI.1.le, hyI.2⟩
      have hden : 2 - Real.cos 0 - Real.cos y ≠ 0 := by
        have hycos := ons_cos_lt_one_of_mem_Icc hyIcc hy0
        rw [Real.cos_zero]
        linarith
      simpa [c] using ons_logGIntBetaDeriv_betaC 0 y hden
    rw [heq, hconst]
  · have heq : (∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC x y) =
        ∫ _y in (-Real.pi)..Real.pi, c := by
      apply intervalIntegral.integral_congr
      intro y _hy
      have hden := (ons_criticalDenom_pos_of_mem_Icc_left hx hx0 (y := y)).ne'
      simpa [c] using ons_logGIntBetaDeriv_betaC x y hden
    rw [heq, hconst]

theorem ons_criticalFirst_double_integral :
    (∫ x in (-Real.pi)..Real.pi,
      ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC x y) =
      8 * Real.pi ^ 2 * Real.cosh (2 * ons_betaC) := by
  calc
    (∫ x in (-Real.pi)..Real.pi,
      ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv ons_betaC x y) =
        ∫ _x in (-Real.pi)..Real.pi,
          (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
            exact ons_criticalFirst_inner_integral x hx
    _ = 8 * Real.pi ^ 2 * Real.cosh (2 * ons_betaC) := by
      rw [intervalIntegral.integral_const]
      norm_num only [smul_eq_mul]
      ring



theorem ons_criticalFirst_normalized_integral :
    (1 / (8 * Real.pi ^ 2)) *
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv ons_betaC x y) =
      Real.cosh (2 * ons_betaC) := by
  rw [ons_criticalFirst_double_integral]
  field_simp [Real.pi_ne_zero]

theorem ons_cosh_betaC_eq_sqrt_two :
    Real.cosh (2 * ons_betaC) = Real.sqrt 2 := by
  have hc := ons_cosh_betaC_sq
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hcpos := Real.cosh_pos (2 * ons_betaC)
  have hsnonneg := Real.sqrt_nonneg 2
  nlinarith

theorem ons_criticalFirst_normalized_integral_eq_sqrt_two :
    (1 / (8 * Real.pi ^ 2)) *
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv ons_betaC x y) = Real.sqrt 2 := by
  rw [ons_criticalFirst_normalized_integral, ons_cosh_betaC_eq_sqrt_two]



noncomputable def ons_noncriticalGap (beta : ℝ) : ℝ :=
  |Real.sinh (2 * beta) - 1|

noncomputable def ons_noncriticalNeighborhood (beta : ℝ) : Set ℝ :=
  {b | 0 < b ∧
    ons_noncriticalGap beta / 2 < |Real.sinh (2 * b) - 1| ∧
    |Real.cosh (2 * b)| < |Real.cosh (2 * beta)| + 1 ∧
    |Real.sinh (2 * b)| < |Real.sinh (2 * beta)| + 1}

theorem ons_noncriticalGap_pos {beta : ℝ} (hbeta : 0 < beta)
    (hcrit : beta ≠ ons_betaC) :
    0 < ons_noncriticalGap beta := by
  have hsne : Real.sinh (2 * beta) ≠ 1 := by
    intro hs
    exact hcrit ((ons_betaC_unique beta hbeta).mp hs)
  exact abs_pos.mpr (sub_ne_zero.mpr hsne)

theorem ons_noncriticalNeighborhood_mem_nhds {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    ons_noncriticalNeighborhood beta ∈ nhds beta := by
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  have hlin : Continuous (fun b : ℝ => 2 * b) := continuous_const.mul continuous_id
  have hsinh : Continuous (fun b : ℝ => Real.sinh (2 * b)) :=
    Real.continuous_sinh.comp hlin
  have hcosh : Continuous (fun b : ℝ => Real.cosh (2 * b)) :=
    Real.continuous_cosh.comp hlin
  have hpos : ∀ᶠ b : ℝ in nhds beta, 0 < b := eventually_gt_nhds hbeta
  have hgapEv : ∀ᶠ b : ℝ in nhds beta,
      ons_noncriticalGap beta / 2 < |Real.sinh (2 * b) - 1| := by
    apply continuousAt_const.eventually_lt ((hsinh.sub continuous_const).abs.continuousAt)
    change ons_noncriticalGap beta / 2 < ons_noncriticalGap beta
    linarith
  have hcoshEv : ∀ᶠ b : ℝ in nhds beta,
      |Real.cosh (2 * b)| < |Real.cosh (2 * beta)| + 1 := by
    apply hcosh.abs.continuousAt.eventually_lt continuousAt_const
    linarith
  have hsinhEv : ∀ᶠ b : ℝ in nhds beta,
      |Real.sinh (2 * b)| < |Real.sinh (2 * beta)| + 1 := by
    apply hsinh.abs.continuousAt.eventually_lt continuousAt_const
    linarith
  filter_upwards [hpos, hgapEv, hcoshEv, hsinhEv] with b hb hbg hbc hbs
  exact ⟨hb, hbg, hbc, hbs⟩

theorem ons_gInt_uniform_lower_noncritical {beta b k1 k2 : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    (ons_noncriticalGap beta / 2) ^ 2 ≤ ons_gInt b k1 k2 := by
  have hsinh0 : 0 ≤ Real.sinh (2 * b) := by
    rw [Real.sinh_nonneg_iff]
    linarith [hb.1]
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  rw [ons_gInt_decompose]
  have hgap0 := ons_noncriticalGap_pos hbeta hcrit
  have habs := hb.2.1
  have hsq : (ons_noncriticalGap beta / 2) ^ 2 ≤
      (Real.sinh (2 * b) - 1) ^ 2 := by
    nlinarith [sq_abs (Real.sinh (2 * b) - 1)]
  nlinarith [mul_nonneg hsinh0 hA]

theorem ons_gInt_pos_noncriticalNeighborhood {beta b k1 k2 : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    0 < ons_gInt b k1 k2 := by
  have hgap0 := ons_noncriticalGap_pos hbeta hcrit
  exact lt_of_lt_of_le (sq_pos_of_pos (div_pos hgap0 two_pos))
    (ons_gInt_uniform_lower_noncritical hbeta hcrit hb)



theorem ons_logGIntBetaDeriv_abs_le_noncritical {beta b k1 k2 : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    |ons_logGIntBetaDeriv b k1 k2| ≤
      (2 * (|Real.cosh (2 * beta)| + 1) *
          (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
        (ons_noncriticalGap beta / 2) ^ 2 := by
  have hgap0 := ons_noncriticalGap_pos hbeta hcrit
  have hden := ons_gInt_uniform_lower_noncritical (k1 := k1) (k2 := k2) hbeta hcrit hb
  have hdenpos := ons_gInt_pos_noncriticalNeighborhood (k1 := k1) (k2 := k2) hbeta hcrit hb
  have hcosh : |Real.cosh (2 * b)| ≤ |Real.cosh (2 * beta)| + 1 := hb.2.2.1.le
  have hsinh : |Real.sinh (2 * b)| ≤ |Real.sinh (2 * beta)| + 1 := hb.2.2.2.le
  have hinner :
      |2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2| ≤
        2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
    calc
      |2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2| ≤
          |2 * Real.sinh (2 * b)| + |Real.cos k1| + |Real.cos k2| := by
            linarith [abs_sub (2 * Real.sinh (2 * b) - Real.cos k1) (Real.cos k2),
              abs_sub (2 * Real.sinh (2 * b)) (Real.cos k1)]
      _ ≤ 2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
        rw [abs_mul]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [Real.abs_cos_le_one k1, Real.abs_cos_le_one k2]
  have hnum : |ons_gIntBetaDeriv b k1 k2| ≤
      2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2) := by
    rw [ons_gIntBetaDeriv, abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hcnonneg : 0 ≤ |Real.cosh (2 * beta)| + 1 := by positivity
    have hinnonneg : 0 ≤
        2 * (|Real.sinh (2 * beta)| + 1) + 2 := by positivity
    nlinarith [mul_le_mul hcosh hinner (abs_nonneg _) hcnonneg]
  rw [ons_logGIntBetaDeriv, abs_div, abs_of_pos hdenpos]
  have hC : 0 ≤ 2 * (|Real.cosh (2 * beta)| + 1) *
      (2 * (|Real.sinh (2 * beta)| + 1) + 2) := by positivity
  exact div_le_div₀ hC hnum
    (sq_pos_of_pos (div_pos hgap0 two_pos)) hden

theorem ons_log_gInt_continuous_momenta_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => Real.log (ons_gInt b p.1 p.2)) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gInt b p.1 p.2) := by
    unfold ons_gInt
    fun_prop
  exact hg.log fun p =>
    (ons_gInt_pos_noncriticalNeighborhood (k1 := p.1) (k2 := p.2)
      hbeta hcrit hb).ne'

theorem ons_logGIntBetaDeriv_continuous_momenta_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => ons_logGIntBetaDeriv b p.1 p.2) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gInt b p.1 p.2) := by
    unfold ons_gInt
    fun_prop
  have hd : Continuous (fun p : ℝ × ℝ => ons_gIntBetaDeriv b p.1 p.2) := by
    unfold ons_gIntBetaDeriv
    fun_prop
  exact hd.div hg fun p =>
    (ons_gInt_pos_noncriticalNeighborhood (k1 := p.1) (k2 := p.2)
      hbeta hcrit hb).ne'



theorem ons_hasDerivAt_innerIntegral_noncritical (beta k1 : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt
      (fun b => ∫ k2 in (-Real.pi)..Real.pi,
        Real.log (ons_gInt b k1 k2))
      (∫ k2 in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv beta k1 k2) beta := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta / 2) ^ 2
  have hself : beta ∈ ons_noncriticalNeighborhood beta :=
    mem_of_mem_nhds (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b k2 => Real.log (ons_gInt b k1 k2))
    (F' := fun b k2 => ons_logGIntBetaDeriv b k1 k2)
    (bound := fun _ => C)
    (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ons_noncriticalNeighborhood_mem_nhds hbeta hcrit] with b hb
    exact ((ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hb).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ((ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hself).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((ons_logGIntBetaDeriv_continuous_momenta_noncritical hbeta hcrit hself).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with k2 _hk2 b hb
    simpa only [Real.norm_eq_abs, C] using
      (ons_logGIntBetaDeriv_abs_le_noncritical (k1 := k1) (k2 := k2)
        hbeta hcrit hb)
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k2 _hk2 b hb
    exact ons_hasDerivAt_log_gInt b k1 k2
      (ons_gInt_pos_noncriticalNeighborhood (k1 := k1) (k2 := k2)
        hbeta hcrit hb).ne'

theorem ons_noncriticalNeighborhood_ne_betaC {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    b ≠ ons_betaC := by
  intro heq
  subst b
  have hzero := hb.2.1
  change ons_noncriticalGap beta / 2 <
    |Real.sinh (2 * ons_betaC) - 1| at hzero
  rw [ons_betaC_sinh, sub_self, abs_zero] at hzero
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  linarith

theorem ons_innerLogIntegral_continuous_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Real.log (ons_gInt b k1 k2)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_log_gInt_continuous_momenta_noncritical hbeta hcrit hb)
    (-Real.pi) Real.pi

theorem ons_innerLogDerivIntegral_continuous_noncritical {beta b : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hb : b ∈ ons_noncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv b k1 k2) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_logGIntBetaDeriv_continuous_momenta_noncritical hbeta hcrit hb)
    (-Real.pi) Real.pi



theorem ons_hasDerivAt_doubleIntegral_noncritical (beta : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt
      (fun b => ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi, Real.log (ons_gInt b k1 k2))
      (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv beta k1 k2) beta := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta / 2) ^ 2
  let B : ℝ := C * (2 * Real.pi)
  have hself : beta ∈ ons_noncriticalNeighborhood beta :=
    mem_of_mem_nhds (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Real.log (ons_gInt b k1 k2))
    (F' := fun b k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv b k1 k2)
    (bound := fun _ => B)
    (ons_noncriticalNeighborhood_mem_nhds hbeta hcrit) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ons_noncriticalNeighborhood_mem_nhds hbeta hcrit] with b hb
    exact (ons_innerLogIntegral_continuous_noncritical hbeta hcrit hb).aestronglyMeasurable
  · exact (ons_innerLogIntegral_continuous_noncritical hbeta hcrit hself).intervalIntegrable _ _
  · exact (ons_innerLogDerivIntegral_continuous_noncritical hbeta hcrit hself).aestronglyMeasurable
  · filter_upwards [] with k1 _hk1 b hb
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (f := fun k2 => ons_logGIntBetaDeriv b k1 k2) (C := C)
      (fun (k2 : ℝ) _hk2 => by
        simpa only [Real.norm_eq_abs, C] using
          (ons_logGIntBetaDeriv_abs_le_noncritical (k1 := k1) (k2 := k2)
            hbeta hcrit hb))
    calc
      ‖∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv b k1 k2‖ ≤
          C * |Real.pi - (-Real.pi)| := hbound
      _ = B := by
        rw [abs_of_pos (show 0 < Real.pi - (-Real.pi) by
          linarith [Real.pi_pos])]
        simp only [B]
        ring
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k1 _hk1 b hb
    exact ons_hasDerivAt_innerIntegral_noncritical b k1 hb.1
      (ons_noncriticalNeighborhood_ne_betaC hbeta hcrit hb)



theorem ons_hasDerivAt_freeEnergyIntegral_noncritical (beta : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt ons_freeEnergyIntegral
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv beta k1 k2) beta := by
  unfold ons_freeEnergyIntegral
  exact (ons_hasDerivAt_doubleIntegral_noncritical beta hbeta hcrit).const_mul
    (1 / (8 * Real.pi ^ 2))

theorem ons_hasDerivAt_pressure_noncritical (beta : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    HasDerivAt ons_pressure
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv beta k1 k2) beta := by
  change HasDerivAt (fun b => Real.log 2 + ons_freeEnergyIntegral b) _ beta
  simpa only [Pi.add_apply, zero_add] using (hasDerivAt_const beta (Real.log 2)).add
    (ons_hasDerivAt_freeEnergyIntegral_noncritical beta hbeta hcrit)



noncomputable def ons_criticalParameterNeighborhood : Set ℝ :=
  {b | (1 / 2 : ℝ) < Real.sinh (2 * b) ∧ |Real.cosh (2 * b)| < 2}

theorem ons_criticalParameterNeighborhood_mem_nhds :
    ons_criticalParameterNeighborhood ∈ nhds ons_betaC := by
  have hlin : Continuous (fun b : ℝ => 2 * b) := continuous_const.mul continuous_id
  have hsinh : Continuous (fun b : ℝ => Real.sinh (2 * b)) :=
    Real.continuous_sinh.comp hlin
  have hcosh : Continuous (fun b : ℝ => Real.cosh (2 * b)) :=
    Real.continuous_cosh.comp hlin
  have hsinhEv : ∀ᶠ b : ℝ in nhds ons_betaC,
      (1 / 2 : ℝ) < Real.sinh (2 * b) := by
    apply continuousAt_const.eventually_lt hsinh.continuousAt
    rw [ons_betaC_sinh]
    norm_num
  have hcoshCrit : |Real.cosh (2 * ons_betaC)| < 2 := by
    rw [abs_of_pos (Real.cosh_pos _)]
    have hsq := ons_cosh_betaC_sq
    nlinarith [Real.cosh_pos (2 * ons_betaC)]
  have hcoshEv : ∀ᶠ b : ℝ in nhds ons_betaC,
      |Real.cosh (2 * b)| < 2 := by
    exact hcosh.abs.continuousAt.eventually_lt continuousAt_const hcoshCrit
  filter_upwards [hsinhEv, hcoshEv] with b hs hc
  exact ⟨hs, hc⟩

theorem ons_gInt_lower_criticalNeighborhood {b k1 k2 : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    (Real.sinh (2 * b) - 1) ^ 2 +
        (2 - Real.cos k1 - Real.cos k2) / 4 ≤ ons_gInt b k1 k2 := by
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  rw [ons_gInt_decompose]
  have hs : 1 / 2 ≤ Real.sinh (2 * b) := hb.1.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hA]

theorem ons_gIntBetaDeriv_abs_le_criticalNeighborhood {b k1 k2 : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    |ons_gIntBetaDeriv b k1 k2| ≤
      4 * (2 * |Real.sinh (2 * b) - 1| +
        (2 - Real.cos k1 - Real.cos k2)) := by
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  have hid : 2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2 =
      2 * (Real.sinh (2 * b) - 1) +
        (2 - Real.cos k1 - Real.cos k2) := by ring
  rw [ons_gIntBetaDeriv, abs_mul, abs_mul, hid]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hinner : |2 * (Real.sinh (2 * b) - 1) +
      (2 - Real.cos k1 - Real.cos k2)| ≤
      2 * |Real.sinh (2 * b) - 1| +
        (2 - Real.cos k1 - Real.cos k2) := by
    calc
      _ ≤ |2 * (Real.sinh (2 * b) - 1)| +
          |2 - Real.cos k1 - Real.cos k2| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hA]
  have hc : |Real.cosh (2 * b)| ≤ 2 := hb.2.le
  nlinarith [mul_le_mul hc hinner (abs_nonneg _)
    (show 0 ≤ (2 : ℝ) from zero_le_two)]

theorem ons_delta_ratio_le_inv_sqrt {delta A : ℝ} (hA : 0 < A) :
    (2 * |delta| + A) / (delta ^ 2 + A) ≤ 1 / Real.sqrt A + 1 := by
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsqrtSq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
  have hden : 0 < delta ^ 2 + A := by positivity
  have hamgm : 2 * |delta| * Real.sqrt A ≤ delta ^ 2 + A := by
    nlinarith [sq_nonneg (|delta| - Real.sqrt A), sq_abs delta]
  rw [div_le_iff₀ hden]
  have hscaled : 2 * |delta| ≤ (delta ^ 2 + A) / Real.sqrt A := by
    exact (le_div_iff₀ hsqrt).2 (by simpa [mul_assoc] using hamgm)
  calc
    2 * |delta| + A ≤
        (delta ^ 2 + A) / Real.sqrt A + (delta ^ 2 + A) := by
          gcongr
          exact le_add_of_nonneg_left (sq_nonneg delta)
    _ = (1 / Real.sqrt A + 1) * (delta ^ 2 + A) := by ring

theorem ons_delta_ratio_quarter_le_inv_sqrt {delta A : ℝ} (hA : 0 < A) :
    (2 * |delta| + A) / (delta ^ 2 + A / 4) ≤
      8 * (1 / Real.sqrt A + 1) := by
  have hquarter : 0 < A / 4 := by positivity
  have hden : 0 < delta ^ 2 + A / 4 := by positivity
  have hbase := ons_delta_ratio_le_inv_sqrt (delta := delta) hquarter
  have hnum : 2 * |delta| + A ≤ 4 * (2 * |delta| + A / 4) := by
    nlinarith [abs_nonneg delta]
  calc
    (2 * |delta| + A) / (delta ^ 2 + A / 4) ≤
        4 * ((2 * |delta| + A / 4) / (delta ^ 2 + A / 4)) := by
          rw [← mul_div_assoc]
          exact (div_le_div_iff_of_pos_right hden).2 hnum
    _ ≤ 4 * (1 / Real.sqrt (A / 4) + 1) := by gcongr
    _ = 4 * (2 / Real.sqrt A + 1) := by
      rw [Real.sqrt_div (le_of_lt hA)]
      norm_num
    _ ≤ 8 * (1 / Real.sqrt A + 1) := by
      have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
      field_simp
      nlinarith

theorem ons_logGIntBetaDeriv_abs_le_criticalA {b k1 k2 : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hA : 0 < 2 - Real.cos k1 - Real.cos k2) :
    |ons_logGIntBetaDeriv b k1 k2| ≤
      32 * (1 / Real.sqrt (2 - Real.cos k1 - Real.cos k2) + 1) := by
  let A : ℝ := 2 - Real.cos k1 - Real.cos k2
  let delta : ℝ := Real.sinh (2 * b) - 1
  have hden0 : 0 < delta ^ 2 + A / 4 := by dsimp [A]; positivity
  have hgLower : delta ^ 2 + A / 4 ≤ ons_gInt b k1 k2 := by
    simpa only [A, delta] using ons_gInt_lower_criticalNeighborhood hb
  have hgPos : 0 < ons_gInt b k1 k2 := hden0.trans_le hgLower
  have hnum := ons_gIntBetaDeriv_abs_le_criticalNeighborhood
    (k1 := k1) (k2 := k2) hb
  change |ons_gIntBetaDeriv b k1 k2 / ons_gInt b k1 k2| ≤ _
  rw [abs_div, abs_of_pos hgPos]
  calc
    |ons_gIntBetaDeriv b k1 k2| / ons_gInt b k1 k2 ≤
        (4 * (2 * |delta| + A)) / (delta ^ 2 + A / 4) := by
          apply div_le_div₀
          · positivity
          · simpa only [A, delta] using hnum
          · exact hden0
          · exact hgLower
    _ = 4 * ((2 * |delta| + A) / (delta ^ 2 + A / 4)) := by ring
    _ ≤ 4 * (8 * (1 / Real.sqrt A + 1)) := by
      gcongr
      exact ons_delta_ratio_quarter_le_inv_sqrt (by simpa only [A] using hA)
    _ = 32 * (1 / Real.sqrt A + 1) := by
      ring
    _ = 32 * (1 / Real.sqrt (2 - Real.cos k1 - Real.cos k2) + 1) := by
      rfl

theorem ons_criticalDenom_lower_abs_mul {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * y| / Real.pi ^ 2 ≤ 2 - Real.cos x - Real.cos y := by
  have hpSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hxabs : |x| ≤ Real.pi := abs_le.mpr hx
  have hyabs : |y| ≤ Real.pi := abs_le.mpr hy
  have hxcos := Real.cos_le_one_sub_mul_cos_sq hxabs
  have hycos := Real.cos_le_one_sub_mul_cos_sq hyabs
  have hxquad : 2 * x ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos x) := by
    have hdiv : (2 * x ^ 2) / Real.pi ^ 2 ≤ 1 - Real.cos x := by
      convert (show 2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x by linarith) using 1
      all_goals ring
    have h := (div_le_iff₀ hpSq).mp hdiv
    nlinarith
  have hyquad : 2 * y ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos y) := by
    have hdiv : (2 * y ^ 2) / Real.pi ^ 2 ≤ 1 - Real.cos y := by
      convert (show 2 / Real.pi ^ 2 * y ^ 2 ≤ 1 - Real.cos y by linarith) using 1
      all_goals ring
    have h := (div_le_iff₀ hpSq).mp hdiv
    nlinarith
  have habs : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  apply (div_le_iff₀ hpSq).2
  nlinarith

theorem ons_inv_sqrt_criticalDenom_le_product {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤
      Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) := by
  have hxy : 0 < |x * y| := abs_pos.mpr (mul_ne_zero hx0 hy0)
  have hpSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hA := ons_criticalDenom_lower_abs_mul hx hy
  have hApos : 0 < 2 - Real.cos x - Real.cos y :=
    (div_pos hxy hpSq).trans_le hA
  have hsA : 0 < Real.sqrt (2 - Real.cos x - Real.cos y) := Real.sqrt_pos.2 hApos
  have hsxy : 0 < Real.sqrt |x * y| := Real.sqrt_pos.2 hxy
  have hsxy_le : Real.sqrt |x * y| ≤
      Real.pi * Real.sqrt (2 - Real.cos x - Real.cos y) := by
    have hsxySq := Real.sq_sqrt hxy.le
    have hsASq := Real.sq_sqrt hApos.le
    have hscaled : |x * y| ≤ Real.pi ^ 2 *
        (2 - Real.cos x - Real.cos y) := by
      simpa only [mul_comm] using (div_le_iff₀ hpSq).mp hA
    have hsquare : (Real.sqrt |x * y|) ^ 2 ≤
        (Real.pi * Real.sqrt (2 - Real.cos x - Real.cos y)) ^ 2 := by
      rw [hsxySq, mul_pow, hsASq]
      exact hscaled
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg Real.pi_pos.le
      (Real.sqrt_nonneg _))).mp hsquare
  have hinv : 1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤
      Real.pi / Real.sqrt |x * y| := by
    rw [div_le_div_iff₀ hsA hsxy]
    simpa [mul_comm] using hsxy_le
  calc
    1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤
        Real.pi / Real.sqrt |x * y| := hinv
    _ = Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) := by
      rw [abs_mul, Real.sqrt_mul (abs_nonneg x)]
      field_simp [Real.sqrt_ne_zero'.mpr (abs_pos.mpr hx0),
        Real.sqrt_ne_zero'.mpr (abs_pos.mpr hy0)]

theorem ons_logGIntBetaDeriv_abs_le_criticalProduct {b x y : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    |ons_logGIntBetaDeriv b x y| ≤
      32 * (Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) + 1) := by
  have hApos : 0 < 2 - Real.cos x - Real.cos y := by
    have hxy : 0 < |x * y| := abs_pos.mpr (mul_ne_zero hx0 hy0)
    have hpSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    exact (div_pos hxy hpSq).trans_le (ons_criticalDenom_lower_abs_mul hx hy)
  calc
    |ons_logGIntBetaDeriv b x y| ≤
        32 * (1 / Real.sqrt (2 - Real.cos x - Real.cos y) + 1) :=
      ons_logGIntBetaDeriv_abs_le_criticalA hb hApos
    _ ≤ 32 * (Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) + 1) := by
      gcongr
      exact ons_inv_sqrt_criticalDenom_le_product hx hy hx0 hy0

theorem ons_criticalParameterNeighborhood_isOpen :
    IsOpen ons_criticalParameterNeighborhood := by
  have hlin : Continuous (fun b : ℝ => 2 * b) := continuous_const.mul continuous_id
  have hsinh : Continuous (fun b : ℝ => Real.sinh (2 * b)) :=
    Real.continuous_sinh.comp hlin
  have hcoshAbs : Continuous (fun b : ℝ => |Real.cosh (2 * b)|) :=
    (Real.continuous_cosh.comp hlin).abs
  change IsOpen ({b : ℝ | (1 / 2 : ℝ) < Real.sinh (2 * b)} ∩
    {b : ℝ | |Real.cosh (2 * b)| < 2})
  exact (isOpen_lt continuous_const hsinh).inter
    (isOpen_lt hcoshAbs continuous_const)

noncomputable def ons_criticalOneDimMajorant (x : ℝ) : ℝ :=
  1 / Real.sqrt |x|

theorem ons_one_div_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt x = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx]

theorem ons_criticalOneDimMajorant_intervalIntegrable :
    IntervalIntegrable ons_criticalOneDimMajorant MeasureTheory.volume
      (-Real.pi) Real.pi := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 Real.pi :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpos : IntervalIntegrable ons_criticalOneDimMajorant
      MeasureTheory.volume 0 Real.pi := by
    apply hpow.congr
    intro x hx
    rw [Set.uIoc_of_le Real.pi_pos.le] at hx
    simp only [ons_criticalOneDimMajorant, abs_of_nonneg hx.1.le]
    exact (ons_one_div_sqrt_eq_rpow_neg_half hx.1.le).symm
  have hnegRaw := hpos.comp_mul_left (c := (-1 : ℝ))
  have hnegOriented : IntervalIntegrable
      (fun x => ons_criticalOneDimMajorant (-x))
      MeasureTheory.volume 0 (-Real.pi) := by
    simpa only [zero_div, div_neg, div_one, neg_mul, one_mul, neg_zero] using hnegRaw
  have hnegOriented' : IntervalIntegrable ons_criticalOneDimMajorant
      MeasureTheory.volume 0 (-Real.pi) := by
    apply hnegOriented.congr
    intro x _hx
    simp [ons_criticalOneDimMajorant]
  exact hnegOriented'.symm.trans hpos

noncomputable def ons_criticalProductMajorant (x y : ℝ) : ℝ :=
  32 * (Real.pi * ons_criticalOneDimMajorant x *
    ons_criticalOneDimMajorant y + 1)

theorem ons_criticalProductMajorant_inner_intervalIntegrable (x : ℝ) :
    IntervalIntegrable (ons_criticalProductMajorant x)
      MeasureTheory.volume (-Real.pi) Real.pi := by
  unfold ons_criticalProductMajorant
  exact ((ons_criticalOneDimMajorant_intervalIntegrable.const_mul
    (Real.pi * ons_criticalOneDimMajorant x)).add
      intervalIntegral.intervalIntegrable_const).const_mul 32

theorem ons_logGIntBetaDeriv_abs_le_criticalMajorant {b x y : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    |ons_logGIntBetaDeriv b x y| ≤ ons_criticalProductMajorant x y := by
  simpa only [ons_criticalProductMajorant, ons_criticalOneDimMajorant] using
    ons_logGIntBetaDeriv_abs_le_criticalProduct hb hx hy hx0 hy0

theorem ons_criticalDenom_pos_of_left_ne_zero {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < 2 - Real.cos x - Real.cos y :=
  ons_criticalDenom_pos_of_mem_Icc_left hx hx0

theorem ons_gInt_pos_criticalNeighborhood_of_left_ne_zero {b x y : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    0 < ons_gInt b x y := by
  have hA := ons_criticalDenom_pos_of_left_ne_zero (y := y) hx hx0
  have hlower := ons_gInt_lower_criticalNeighborhood (b := b) (k1 := x) (k2 := y) hb
  exact (by positivity : 0 < (Real.sinh (2 * b) - 1) ^ 2 +
    (2 - Real.cos x - Real.cos y) / 4).trans_le hlower

theorem ons_log_gInt_continuous_right_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y => Real.log (ons_gInt b x y)) := by
  have hg : Continuous (fun y => ons_gInt b x y) := by
    unfold ons_gInt
    fun_prop
  exact hg.log fun y =>
    (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0).ne'

theorem ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    Continuous (fun y => ons_logGIntBetaDeriv b x y) := by
  have hg : Continuous (fun y => ons_gInt b x y) := by
    unfold ons_gInt
    fun_prop
  have hd : Continuous (fun y => ons_gIntBetaDeriv b x y) := by
    unfold ons_gIntBetaDeriv
    fun_prop
  exact hd.div hg fun y =>
    (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0).ne'

theorem ons_ae_ne_zero : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬x ≠ 0} = ({0} : Set ℝ) := by
    ext x
    simp
  rw [hset]
  exact MeasureTheory.measure_singleton 0




theorem ons_hasDerivAt_innerIntegral_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasDerivAt
      (fun beta => ∫ y in (-Real.pi)..Real.pi,
        Real.log (ons_gInt beta x y))
      (∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv b x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun beta y => Real.log (ons_gInt beta x y))
    (F' := fun beta y => ons_logGIntBetaDeriv beta x y)
    (bound := ons_criticalProductMajorant x) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with beta hbeta
    exact (ons_log_gInt_continuous_right_criticalNeighborhood
      hbeta hx hx0).aestronglyMeasurable
  · exact (ons_log_gInt_continuous_right_criticalNeighborhood hb hx hx0).intervalIntegrable _ _
  · exact (ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood
      hb hx hx0).aestronglyMeasurable
  · filter_upwards [ons_ae_ne_zero] with y hy0 hyI beta hbeta
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      ons_logGIntBetaDeriv_abs_le_criticalMajorant hbeta hx hy hx0 hy0
  · exact ons_criticalProductMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI beta hbeta
    exact ons_hasDerivAt_log_gInt beta x y
      (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hbeta hx hx0).ne'

theorem ons_criticalParameterNeighborhood_sinh_bounds {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    (1 / 2 : ℝ) ≤ Real.sinh (2 * b) ∧ Real.sinh (2 * b) ≤ 2 := by
  refine ⟨hb.1.le, ?_⟩
  have hid := Real.cosh_sq_sub_sinh_sq (2 * b)
  have habsSq := sq_abs (Real.cosh (2 * b))
  have hc := hb.2
  have hcSq : |Real.cosh (2 * b)| ^ 2 < (2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg _) zero_le_two).2 hc
  have hspos : 0 < Real.sinh (2 * b) := by linarith [hb.1]
  nlinarith

theorem ons_criticalProductMajorant_inner_integral (x : ℝ) :
    (∫ y in (-Real.pi)..Real.pi, ons_criticalProductMajorant x y) =
      32 * (Real.pi * ons_criticalOneDimMajorant x *
        (∫ y in (-Real.pi)..Real.pi, ons_criticalOneDimMajorant y) +
          2 * Real.pi) := by
  have hfirst : IntervalIntegrable
      (fun y => Real.pi * ons_criticalOneDimMajorant x *
        ons_criticalOneDimMajorant y) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    ons_criticalOneDimMajorant_intervalIntegrable.const_mul
      (Real.pi * ons_criticalOneDimMajorant x)
  unfold ons_criticalProductMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hfirst intervalIntegral.intervalIntegrable_const]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  norm_num only [smul_eq_mul]
  ring

noncomputable def ons_criticalOuterMajorant (x : ℝ) : ℝ :=
  32 * (Real.pi * ons_criticalOneDimMajorant x *
    (∫ y in (-Real.pi)..Real.pi, ons_criticalOneDimMajorant y) +
      2 * Real.pi)

theorem ons_criticalOuterMajorant_intervalIntegrable :
    IntervalIntegrable ons_criticalOuterMajorant MeasureTheory.volume
      (-Real.pi) Real.pi := by
  let J : ℝ := ∫ y in (-Real.pi)..Real.pi, ons_criticalOneDimMajorant y
  have hterm : IntervalIntegrable
      (fun x => Real.pi * ons_criticalOneDimMajorant x * J)
      MeasureTheory.volume (-Real.pi) Real.pi := by
    convert ons_criticalOneDimMajorant_intervalIntegrable.const_mul (Real.pi * J) using 1
    ext x
    ring
  unfold ons_criticalOuterMajorant
  change IntervalIntegrable
    (fun x => 32 * (Real.pi * ons_criticalOneDimMajorant x * J + 2 * Real.pi))
    MeasureTheory.volume (-Real.pi) Real.pi
  exact (hterm.add intervalIntegral.intervalIntegrable_const).const_mul 32

theorem ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ‖∫ y in (-Real.pi)..Real.pi, ons_logGIntBetaDeriv b x y‖ ≤
      ons_criticalOuterMajorant x := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun y => ons_logGIntBetaDeriv b x y)
    (g := ons_criticalProductMajorant x)
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) (by
      filter_upwards [ons_ae_ne_zero] with y hy0 hyI
      have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
        exact ⟨hyI.1.le, hyI.2⟩
      simpa only [Real.norm_eq_abs] using
        ons_logGIntBetaDeriv_abs_le_criticalMajorant hb hx hy hx0 hy0)
    (ons_criticalProductMajorant_inner_intervalIntegrable x)
  rw [ons_criticalProductMajorant_inner_integral] at hnorm
  exact hnorm




theorem ons_hasDerivAt_doubleIntegral_betaC :
    HasDerivAt
      (fun b => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt b x y))
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv ons_betaC x y) ons_betaC := by
  have hself : ons_betaC ∈ ons_criticalParameterNeighborhood :=
    mem_of_mem_nhds ons_criticalParameterNeighborhood_mem_nhds
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (ons_gInt b x y))
    (F' := fun b x => ∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv b x y)
    (bound := ons_criticalOuterMajorant)
    ons_criticalParameterNeighborhood_mem_nhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [ons_criticalParameterNeighborhood_mem_nhds] with b hb
    have hs := ons_criticalParameterNeighborhood_sinh_bounds hb
    exact (ons_inner_integral_continuous_near_betaC b hs.1 hs.2).aestronglyMeasurable
  · exact (ons_inner_integral_continuous_near_betaC ons_betaC
      (by rw [ons_betaC_sinh]; norm_num)
      (by rw [ons_betaC_sinh]; norm_num)).intervalIntegrable _ _
  · apply (continuous_const.aestronglyMeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun _x : ℝ => (2 * Real.pi) * (2 * Real.cosh (2 * ons_betaC)))
        (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi))).congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    have hx' := Set.uIoc_subset_uIcc hx
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx'
    exact (ons_criticalFirst_inner_integral x hx').symm
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI b hb
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hb hx hx0
  · exact ons_criticalOuterMajorant_intervalIntegrable
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI b hb
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_hasDerivAt_innerIntegral_criticalNeighborhood hb hx hx0

theorem ons_hasDerivAt_freeEnergyIntegral_betaC :
    HasDerivAt ons_freeEnergyIntegral (Real.sqrt 2) ons_betaC := by
  have h := ons_hasDerivAt_doubleIntegral_betaC.const_mul
    (1 / (8 * Real.pi ^ 2))
  unfold ons_freeEnergyIntegral
  convert h using 1
  exact ons_criticalFirst_normalized_integral_eq_sqrt_two.symm

theorem ons_hasDerivAt_pressure_betaC :
    HasDerivAt ons_pressure (Real.sqrt 2) ons_betaC := by
  change HasDerivAt (fun b => Real.log 2 + ons_freeEnergyIntegral b)
    (Real.sqrt 2) ons_betaC
  simpa only [Pi.add_apply, zero_add] using
    (hasDerivAt_const ons_betaC (Real.log 2)).add
      ons_hasDerivAt_freeEnergyIntegral_betaC

theorem ons_innerLogDerivIntegral_aestronglyMeasurable (b : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv b x y)
      (MeasureTheory.volume.restrict (Set.uIoc (-Real.pi) Real.pi)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi)
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ons_logGIntBetaDeriv b p.1 p.2) (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    unfold ons_logGIntBetaDeriv ons_gIntBetaDeriv ons_gInt
    fun_prop
  have hi := hjoint.integral_prod_right'
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simpa only [μ, intervalIntegral.integral_of_le hpi,
    Set.uIoc_of_le hpi] using hi

theorem ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood {b x : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    ContinuousAt
      (fun beta => ∫ y in (-Real.pi)..Real.pi,
        ons_logGIntBetaDeriv beta x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (ons_criticalProductMajorant x)
  · filter_upwards [hs] with beta hbeta
    exact (ons_logGIntBetaDeriv_continuous_right_criticalNeighborhood
      hbeta hx hx0).aestronglyMeasurable
  · filter_upwards [hs] with beta hbeta
    filter_upwards [ons_ae_ne_zero] with y hy0 hyI
    have hy : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hyI
      exact ⟨hyI.1.le, hyI.2⟩
    simpa only [Real.norm_eq_abs] using
      ons_logGIntBetaDeriv_abs_le_criticalMajorant hbeta hx hy hx0 hy0
  · exact ons_criticalProductMajorant_inner_intervalIntegrable x
  · filter_upwards [] with y _hyI
    exact (ons_hasDerivAt_logGIntBetaDeriv b x y
      (ons_gInt_pos_criticalNeighborhood_of_left_ne_zero hb hx hx0).ne').continuousAt

theorem ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    ContinuousAt
      (fun beta => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv beta x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    ons_criticalOuterMajorant
  · exact Filter.Eventually.of_forall ons_innerLogDerivIntegral_aestronglyMeasurable
  · filter_upwards [hs] with beta hbeta
    filter_upwards [ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hbeta hx hx0
  · exact ons_criticalOuterMajorant_intervalIntegrable
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_continuousAt_criticalNeighborhood hb hx hx0

theorem ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood :
    ContinuousOn
      (fun beta => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv beta x y)
      ons_criticalParameterNeighborhood := by
  intro b hb
  exact (ons_firstDerivativeDoubleIntegral_continuousAt_criticalNeighborhood hb).continuousWithinAt

theorem ons_hasDerivAt_doubleIntegral_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    HasDerivAt
      (fun beta => ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi, Real.log (ons_gInt beta x y))
      (∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv b x y) b := by
  have hs : ons_criticalParameterNeighborhood ∈ nhds b :=
    ons_criticalParameterNeighborhood_isOpen.mem_nhds hb
  have hsinh := ons_criticalParameterNeighborhood_sinh_bounds hb
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun beta x => ∫ y in (-Real.pi)..Real.pi,
      Real.log (ons_gInt beta x y))
    (F' := fun beta x => ∫ y in (-Real.pi)..Real.pi,
      ons_logGIntBetaDeriv beta x y)
    (bound := ons_criticalOuterMajorant) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with beta hbeta
    have hsbeta := ons_criticalParameterNeighborhood_sinh_bounds hbeta
    exact (ons_inner_integral_continuous_near_betaC beta
      hsbeta.1 hsbeta.2).aestronglyMeasurable
  · exact (ons_inner_integral_continuous_near_betaC b
      hsinh.1 hsinh.2).intervalIntegrable _ _
  · exact ons_innerLogDerivIntegral_aestronglyMeasurable b
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI beta hbeta
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_innerLogDerivIntegral_norm_le_criticalOuterMajorant hbeta hx hx0
  · exact ons_criticalOuterMajorant_intervalIntegrable
  · filter_upwards [ons_ae_ne_zero] with x hx0 hxI beta hbeta
    have hx : x ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    exact ons_hasDerivAt_innerIntegral_criticalNeighborhood hbeta hx hx0

theorem ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    HasDerivAt ons_freeEnergyIntegral
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ x in (-Real.pi)..Real.pi,
          ∫ y in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv b x y) b := by
  unfold ons_freeEnergyIntegral
  exact (ons_hasDerivAt_doubleIntegral_criticalNeighborhood hb).const_mul
    (1 / (8 * Real.pi ^ 2))

theorem ons_hasDerivAt_pressure_criticalNeighborhood {b : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    HasDerivAt ons_pressure
      ((1 / (8 * Real.pi ^ 2)) *
        ∫ x in (-Real.pi)..Real.pi,
          ∫ y in (-Real.pi)..Real.pi,
            ons_logGIntBetaDeriv b x y) b := by
  change HasDerivAt (fun beta => Real.log 2 + ons_freeEnergyIntegral beta) _ b
  simpa only [Pi.add_apply, zero_add] using
    (hasDerivAt_const b (Real.log 2)).add
      (ons_hasDerivAt_freeEnergyIntegral_criticalNeighborhood hb)




theorem ons_pressure_contDiffAt_one_betaC :
    ContDiffAt ℝ 1 ons_pressure ons_betaC := by
  let d : ℝ → ℝ := fun b =>
    (1 / (8 * Real.pi ^ 2)) *
      ∫ x in (-Real.pi)..Real.pi,
        ∫ y in (-Real.pi)..Real.pi,
          ons_logGIntBetaDeriv b x y
  let f' : ℝ → ℝ →L[ℝ] ℝ := fun b =>
    d b • ContinuousLinearMap.id ℝ ℝ
  rw [contDiffAt_one_iff]
  refine ⟨f', ons_criticalParameterNeighborhood,
    ons_criticalParameterNeighborhood_mem_nhds, ?_, ?_⟩
  · have hd : ContinuousOn d ons_criticalParameterNeighborhood := by
      exact ons_firstDerivativeDoubleIntegral_continuousOn_criticalNeighborhood.const_mul
        (1 / (8 * Real.pi ^ 2))
    exact hd.smul continuousOn_const
  · intro b hb
    rw [hasFDerivAt_iff_hasDerivAt]
    simpa only [f', d, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using
      ons_hasDerivAt_pressure_criticalNeighborhood hb



noncomputable def ons_gIntComplex (z : ℂ) (k1 k2 : ℝ) : ℂ :=
  Complex.cosh (2 * z) ^ 2 -
    Complex.sinh (2 * z) * ((Real.cos k1 : ℂ) + (Real.cos k2 : ℂ))

noncomputable def ons_gIntComplexDeriv (z : ℂ) (k1 k2 : ℝ) : ℂ :=
  2 * Complex.cosh (2 * z) *
    (2 * Complex.sinh (2 * z) - (Real.cos k1 : ℂ) - (Real.cos k2 : ℂ))

theorem ons_gIntComplex_ofReal (beta k1 k2 : ℝ) :
    ons_gIntComplex (beta : ℂ) k1 k2 = (ons_gInt beta k1 k2 : ℂ) := by
  have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
  unfold ons_gIntComplex ons_gInt
  rw [harg, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  rfl

noncomputable def ons_complexNoncriticalDeviation (beta : ℝ) (z : ℂ) : ℝ :=
  ‖Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2‖ +
    2 * ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)‖

noncomputable def ons_complexNoncriticalNeighborhood (beta : ℝ) : Set ℂ :=
  {z | ons_complexNoncriticalDeviation beta z < ons_noncriticalGap beta ^ 2 / 2 ∧
    ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1 ∧
    ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1}

theorem ons_complexNoncriticalDeviation_continuous (beta : ℝ) :
    Continuous (ons_complexNoncriticalDeviation beta) := by
  unfold ons_complexNoncriticalDeviation
  fun_prop

theorem ons_complexCoshNorm_continuous :
    Continuous (fun z : ℂ => ‖Complex.cosh (2 * z)‖) := by
  fun_prop

theorem ons_complexSinhNorm_continuous :
    Continuous (fun z : ℂ => ‖Complex.sinh (2 * z)‖) := by
  fun_prop

theorem ons_complexNoncriticalDeviation_ofReal (beta : ℝ) :
    ons_complexNoncriticalDeviation beta (beta : ℂ) = 0 := by
  have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
  unfold ons_complexNoncriticalDeviation
  rw [harg, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  simp

theorem ons_complexNoncriticalNeighborhood_isOpen (beta : ℝ) :
    IsOpen (ons_complexNoncriticalNeighborhood beta) := by
  change IsOpen
    ({z : ℂ | ons_complexNoncriticalDeviation beta z <
        ons_noncriticalGap beta ^ 2 / 2} ∩
      ({z : ℂ | ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1} ∩
       {z : ℂ | ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1}))
  exact (isOpen_lt (ons_complexNoncriticalDeviation_continuous beta) continuous_const).inter
    ((isOpen_lt ons_complexCoshNorm_continuous continuous_const).inter
      (isOpen_lt ons_complexSinhNorm_continuous continuous_const))

theorem ons_complexNoncriticalNeighborhood_mem_nhds {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    ons_complexNoncriticalNeighborhood beta ∈ nhds (beta : ℂ) := by
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  have hdev : ∀ᶠ z : ℂ in nhds (beta : ℂ),
      ons_complexNoncriticalDeviation beta z < ons_noncriticalGap beta ^ 2 / 2 := by
    apply (ons_complexNoncriticalDeviation_continuous beta).continuousAt.eventually_lt
      continuousAt_const
    rw [ons_complexNoncriticalDeviation_ofReal]
    positivity
  have hcosh : ∀ᶠ z : ℂ in nhds (beta : ℂ),
      ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1 := by
    apply ons_complexCoshNorm_continuous.continuousAt.eventually_lt continuousAt_const
    have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
    rw [harg, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hsinh : ∀ᶠ z : ℂ in nhds (beta : ℂ),
      ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1 := by
    apply ons_complexSinhNorm_continuous.continuousAt.eventually_lt continuousAt_const
    have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
    rw [harg, ← Complex.ofReal_sinh, Complex.norm_real, Real.norm_eq_abs]
    linarith
  filter_upwards [hdev, hcosh, hsinh] with z hz hc hs
  exact ⟨hz, hc, hs⟩

theorem ons_gIntComplex_sub_ofReal_norm_le_deviation
    (beta : ℝ) (z : ℂ) (k1 k2 : ℝ) :
    ‖ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)‖ ≤
      ons_complexNoncriticalDeviation beta z := by
  let q : ℂ := (Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)
  have hq : ‖q‖ ≤ 2 := by
    calc
      ‖q‖ ≤ ‖(Real.cos k1 : ℂ)‖ + ‖(Real.cos k2 : ℂ)‖ := norm_add_le _ _
      _ = |Real.cos k1| + |Real.cos k2| := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 := by nlinarith [Real.abs_cos_le_one k1, Real.abs_cos_le_one k2]
  rw [← ons_gIntComplex_ofReal beta k1 k2]
  have heq : ons_gIntComplex z k1 k2 - ons_gIntComplex (beta : ℂ) k1 k2 =
      (Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2) -
        (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)) * q := by
    have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
    unfold ons_gIntComplex q
    rw [harg, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    ring
  rw [heq]
  calc
    ‖(Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2) -
        (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)) * q‖ ≤
        ‖Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2‖ +
          ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)‖ * ‖q‖ := by
            simpa only [norm_mul] using norm_sub_le
              (Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2)
              ((Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)) * q)
    _ ≤ ‖Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2‖ +
          2 * ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)‖ := by
      nlinarith [norm_nonneg (Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ))]
    _ = ons_complexNoncriticalDeviation beta z := by
      unfold ons_complexNoncriticalDeviation
      ring

theorem ons_gInt_lower_noncritical_base {beta k1 k2 : ℝ}
    (hbeta : 0 < beta) (_hcrit : beta ≠ ons_betaC) :
    ons_noncriticalGap beta ^ 2 ≤ ons_gInt beta k1 k2 := by
  have hs : 0 ≤ Real.sinh (2 * beta) := by
    rw [Real.sinh_nonneg_iff]
    linarith
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  rw [ons_gInt_decompose]
  have hgap : ons_noncriticalGap beta ^ 2 =
      (Real.sinh (2 * beta) - 1) ^ 2 := by
    unfold ons_noncriticalGap
    exact sq_abs _
  rw [hgap]
  exact le_add_of_nonneg_right (mul_nonneg hs hA)

theorem ons_gIntComplex_re_pos_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    0 < (ons_gIntComplex z k1 k2).re := by
  let m : ℝ := ons_noncriticalGap beta ^ 2
  let d : ℂ := ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  have hm : 0 < m := sq_pos_of_pos hgap
  have hdnorm : ‖d‖ < m / 2 :=
    (ons_gIntComplex_sub_ofReal_norm_le_deviation beta z k1 k2).trans_lt hz.1
  have hdre : -‖d‖ ≤ d.re := by
    exact neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hreal := ons_gInt_lower_noncritical_base (k1 := k1) (k2 := k2) hbeta hcrit
  have hre : (ons_gIntComplex z k1 k2).re = ons_gInt beta k1 k2 + d.re := by
    dsimp [d]
    ring_nf
  rw [hre]
  dsimp [m] at hm hdnorm hreal ⊢
  nlinarith

theorem ons_gIntComplex_mem_slitPlane_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    ons_gIntComplex z k1 k2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (ons_gIntComplex_re_pos_noncritical hbeta hcrit hz k1 k2)

theorem ons_gIntComplex_norm_lower_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    ons_noncriticalGap beta ^ 2 / 2 < ‖ons_gIntComplex z k1 k2‖ := by
  let m : ℝ := ons_noncriticalGap beta ^ 2
  let d : ℂ := ons_gIntComplex z k1 k2 - (ons_gInt beta k1 k2 : ℂ)
  have hdnorm : ‖d‖ < m / 2 :=
    (ons_gIntComplex_sub_ofReal_norm_le_deviation beta z k1 k2).trans_lt hz.1
  have hdre : -‖d‖ ≤ d.re := by
    exact neg_le_of_abs_le (Complex.abs_re_le_norm d)
  have hreal := ons_gInt_lower_noncritical_base (k1 := k1) (k2 := k2) hbeta hcrit
  have hre : (ons_gIntComplex z k1 k2).re = ons_gInt beta k1 k2 + d.re := by
    dsimp [d]
    ring_nf
  have hrenorm := Complex.re_le_norm (ons_gIntComplex z k1 k2)
  dsimp [m] at hdnorm hreal ⊢
  rw [hre] at hrenorm
  nlinarith

noncomputable def ons_logGIntComplexDeriv (z : ℂ) (k1 k2 : ℝ) : ℂ :=
  ons_gIntComplexDeriv z k1 k2 / ons_gIntComplex z k1 k2

theorem ons_logGIntComplexDeriv_norm_le_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    ‖ons_logGIntComplexDeriv z k1 k2‖ ≤
      (2 * (|Real.cosh (2 * beta)| + 1) *
          (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
        (ons_noncriticalGap beta ^ 2 / 2) := by
  have hq : ‖Complex.cos (k1 : ℂ) + Complex.cos (k2 : ℂ)‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.cos (k1 : ℂ)‖ + ‖Complex.cos (k2 : ℂ)‖ := norm_add_le _ _
      _ = |Real.cos k1| + |Real.cos k2| := by
        rw [← Complex.ofReal_cos, ← Complex.ofReal_cos]
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 := by nlinarith [Real.abs_cos_le_one k1, Real.abs_cos_le_one k2]
  have hinner : ‖2 * Complex.sinh (2 * z) - (Real.cos k1 : ℂ) - (Real.cos k2 : ℂ)‖ ≤
      2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
    calc
      _ ≤ ‖(2 : ℂ) * Complex.sinh (2 * z)‖ +
          ‖(Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)‖ := by
            convert norm_sub_le ((2 : ℂ) * Complex.sinh (2 * z))
              ((Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)) using 1
            all_goals ring_nf
      _ ≤ 2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
        rw [norm_mul]
        norm_num
        nlinarith [hq, hz.2.2.le, norm_nonneg (Complex.sinh (2 * z))]
  have hnum : ‖ons_gIntComplexDeriv z k1 k2‖ ≤
      2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2) := by
    rw [ons_gIntComplexDeriv, norm_mul, norm_mul]
    norm_num
    have hinner' : ‖2 * Complex.sinh (2 * z) - Complex.cos (k1 : ℂ) -
        Complex.cos (k2 : ℂ)‖ ≤
        2 * (|Real.sinh (2 * beta)| + 1) + 2 := by
      simpa only [Complex.ofReal_cos] using hinner
    exact mul_le_mul (mul_le_mul_of_nonneg_left hz.2.1.le (by positivity))
      hinner' (norm_nonneg _) (by positivity)
  have hden := ons_gIntComplex_norm_lower_noncritical hbeta hcrit hz k1 k2
  have hgap := ons_noncriticalGap_pos hbeta hcrit
  rw [ons_logGIntComplexDeriv, norm_div]
  exact div_le_div₀ (by positivity) hnum (by positivity) hden.le

theorem ons_hasDerivAt_gIntComplex (z : ℂ) (k1 k2 : ℝ) :
    HasDerivAt (fun w => ons_gIntComplex w k1 k2)
      (ons_gIntComplexDeriv z k1 k2) z := by
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    convert (hasDerivAt_id z).const_mul 2 using 1
    all_goals ring
  have hcosh : HasDerivAt (fun w : ℂ => Complex.cosh (2 * w))
      (2 * Complex.sinh (2 * z)) z := by
    convert (Complex.hasDerivAt_cosh (2 * z)).comp z hlin using 1
    all_goals ring
  have hsinh : HasDerivAt (fun w : ℂ => Complex.sinh (2 * w))
      (2 * Complex.cosh (2 * z)) z := by
    convert (Complex.hasDerivAt_sinh (2 * z)).comp z hlin using 1
    all_goals ring
  have h := (hcosh.pow 2).sub
    (hsinh.mul_const ((Real.cos k1 : ℂ) + (Real.cos k2 : ℂ)))
  convert h using 1
  unfold ons_gIntComplexDeriv
  ring

theorem ons_hasDerivAt_log_gIntComplex {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) (k1 k2 : ℝ) :
    HasDerivAt (fun w => Complex.log (ons_gIntComplex w k1 k2))
      (ons_logGIntComplexDeriv z k1 k2) z := by
  simpa only [ons_logGIntComplexDeriv] using
    (ons_hasDerivAt_gIntComplex z k1 k2).clog
      (ons_gIntComplex_mem_slitPlane_noncritical hbeta hcrit hz k1 k2)

theorem ons_complexLogGInt_continuous_momenta_noncritical {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => Complex.log (ons_gIntComplex z p.1 p.2)) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gIntComplex z p.1 p.2) := by
    unfold ons_gIntComplex
    fun_prop
  rw [continuous_iff_continuousAt]
  intro p
  have hlog : ContinuousAt Complex.log (ons_gIntComplex z p.1 p.2) :=
    (Complex.hasDerivAt_log
      (ons_gIntComplex_mem_slitPlane_noncritical hbeta hcrit hz p.1 p.2)).continuousAt
  have hc := ContinuousAt.comp
    (f := fun q : ℝ × ℝ => ons_gIntComplex z q.1 q.2) hlog hg.continuousAt
  simpa only [Function.comp_apply] using hc

theorem ons_logGIntComplexDeriv_continuous_momenta_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun p : ℝ × ℝ => ons_logGIntComplexDeriv z p.1 p.2) := by
  have hg : Continuous (fun p : ℝ × ℝ => ons_gIntComplex z p.1 p.2) := by
    unfold ons_gIntComplex
    fun_prop
  have hd : Continuous (fun p : ℝ × ℝ => ons_gIntComplexDeriv z p.1 p.2) := by
    unfold ons_gIntComplexDeriv
    fun_prop
  exact hd.div hg fun p hzero => by
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (ons_gIntComplex_re_pos_noncritical hbeta hcrit hz p.1 p.2).ne' hre

theorem ons_complexInnerLogIntegral_continuous_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Complex.log (ons_gIntComplex z k1 k2)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem ons_complexInnerLogDerivIntegral_continuous_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    Continuous (fun k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntComplexDeriv z k1 k2) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (ons_logGIntComplexDeriv_continuous_momenta_noncritical hbeta hcrit hz)
    (-Real.pi) Real.pi

theorem ons_hasDerivAt_complexInnerIntegral_noncritical
    {beta : ℝ} {z : ℂ} (k1 : ℝ)
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    HasDerivAt
      (fun w => ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex w k1 k2))
      (∫ k2 in (-Real.pi)..Real.pi,
        ons_logGIntComplexDeriv z k1 k2) z := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta ^ 2 / 2)
  have hs : ons_complexNoncriticalNeighborhood beta ∈ nhds z :=
    (ons_complexNoncriticalNeighborhood_isOpen beta).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w k2 => Complex.log (ons_gIntComplex w k1 k2))
    (F' := fun w k2 => ons_logGIntComplexDeriv w k1 k2)
    (bound := fun _ => C) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact ((ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hw).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ((ons_complexLogGInt_continuous_momenta_noncritical hbeta hcrit hz).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((ons_logGIntComplexDeriv_continuous_momenta_noncritical hbeta hcrit hz).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with k2 _hk2 w hw
    simpa only [C] using
      ons_logGIntComplexDeriv_norm_le_noncritical hbeta hcrit hw k1 k2
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k2 _hk2 w hw
    exact ons_hasDerivAt_log_gIntComplex hbeta hcrit hw k1 k2

theorem ons_hasDerivAt_complexDoubleIntegral_noncritical
    {beta : ℝ} {z : ℂ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC)
    (hz : z ∈ ons_complexNoncriticalNeighborhood beta) :
    HasDerivAt
      (fun w => ∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Complex.log (ons_gIntComplex w k1 k2))
      (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntComplexDeriv z k1 k2) z := by
  let C : ℝ :=
    (2 * (|Real.cosh (2 * beta)| + 1) *
        (2 * (|Real.sinh (2 * beta)| + 1) + 2)) /
      (ons_noncriticalGap beta ^ 2 / 2)
  let B : ℝ := C * (2 * Real.pi)
  have hs : ons_complexNoncriticalNeighborhood beta ∈ nhds z :=
    (ons_complexNoncriticalNeighborhood_isOpen beta).mem_nhds hz
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w k1 => ∫ k2 in (-Real.pi)..Real.pi,
      Complex.log (ons_gIntComplex w k1 k2))
    (F' := fun w k1 => ∫ k2 in (-Real.pi)..Real.pi,
      ons_logGIntComplexDeriv w k1 k2)
    (bound := fun _ => B) hs ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hs] with w hw
    exact (ons_complexInnerLogIntegral_continuous_noncritical
      hbeta hcrit hw).aestronglyMeasurable
  · exact (ons_complexInnerLogIntegral_continuous_noncritical hbeta hcrit hz).intervalIntegrable _ _
  · exact (ons_complexInnerLogDerivIntegral_continuous_noncritical
      hbeta hcrit hz).aestronglyMeasurable
  · filter_upwards [] with k1 _hk1 w hw
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -Real.pi) (b := Real.pi)
      (f := fun k2 => ons_logGIntComplexDeriv w k1 k2) (C := C)
      (fun (k2 : ℝ) _hk2 => by
        simpa only [C] using
          ons_logGIntComplexDeriv_norm_le_noncritical hbeta hcrit hw k1 k2)
    calc
      ‖∫ k2 in (-Real.pi)..Real.pi,
          ons_logGIntComplexDeriv w k1 k2‖ ≤
          C * |Real.pi - (-Real.pi)| := hbound
      _ = B := by
        rw [abs_of_pos (show 0 < Real.pi - (-Real.pi) by
          linarith [Real.pi_pos])]
        simp only [B]
        ring
  · exact intervalIntegral.intervalIntegrable_const
  · filter_upwards [] with k1 _hk1 w hw
    exact ons_hasDerivAt_complexInnerIntegral_noncritical k1 hbeta hcrit hw

noncomputable def ons_freeEnergyIntegralComplex (z : ℂ) : ℂ :=
  (1 / (8 * Real.pi ^ 2) : ℂ) *
    ∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex z k1 k2)

noncomputable def ons_pressureComplex (z : ℂ) : ℂ :=
  (Real.log 2 : ℂ) + ons_freeEnergyIntegralComplex z

theorem ons_pressureComplex_differentiableOn_noncritical {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    DifferentiableOn ℂ ons_pressureComplex
      (ons_complexNoncriticalNeighborhood beta) := by
  intro z hz
  have hdouble := ons_hasDerivAt_complexDoubleIntegral_noncritical hbeta hcrit hz
  unfold ons_pressureComplex ons_freeEnergyIntegralComplex
  exact ((hasDerivAt_const z (Real.log 2 : ℂ)).add
    (hdouble.const_mul (1 / (8 * Real.pi ^ 2) : ℂ))).differentiableAt.differentiableWithinAt

theorem ons_pressureComplex_analyticAt_noncritical {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    AnalyticAt ℂ ons_pressureComplex (beta : ℂ) := by
  exact (ons_pressureComplex_differentiableOn_noncritical hbeta hcrit).analyticAt
    (ons_complexNoncriticalNeighborhood_mem_nhds hbeta hcrit)

theorem ons_complexLogGInt_ofReal {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) (k1 k2 : ℝ) :
    Complex.log (ons_gIntComplex (beta : ℂ) k1 k2) =
      (Real.log (ons_gInt beta k1 k2) : ℂ) := by
  rw [ons_gIntComplex_ofReal]
  exact (Complex.ofReal_log
    (le_trans (sq_nonneg _) (ons_gInt_lower_noncritical_base hbeta hcrit))).symm

theorem ons_complexDoubleIntegral_ofReal {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    (∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) =
      Complex.ofReal (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (ons_gInt beta k1 k2)) := by
  calc
    (∫ k1 in (-Real.pi)..Real.pi,
      ∫ k2 in (-Real.pi)..Real.pi,
        Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) =
        ∫ k1 in (-Real.pi)..Real.pi,
          Complex.ofReal (∫ k2 in (-Real.pi)..Real.pi,
            Real.log (ons_gInt beta k1 k2)) := by
              apply intervalIntegral.integral_congr
              intro k1 _hk1
              calc
                (∫ k2 in (-Real.pi)..Real.pi,
                  Complex.log (ons_gIntComplex (beta : ℂ) k1 k2)) =
                    ∫ k2 in (-Real.pi)..Real.pi,
                      (Real.log (ons_gInt beta k1 k2) : ℂ) := by
                        apply intervalIntegral.integral_congr
                        intro k2 _hk2
                        exact ons_complexLogGInt_ofReal hbeta hcrit k1 k2
                _ = Complex.ofReal (∫ k2 in (-Real.pi)..Real.pi,
                    Real.log (ons_gInt beta k1 k2)) :=
                  intervalIntegral.integral_ofReal
    _ = Complex.ofReal (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (ons_gInt beta k1 k2)) :=
      intervalIntegral.integral_ofReal

theorem ons_pressureComplex_ofReal {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    ons_pressureComplex (beta : ℂ) = (ons_pressure beta : ℂ) := by
  unfold ons_pressureComplex ons_freeEnergyIntegralComplex
  rw [ons_complexDoubleIntegral_ofReal hbeta hcrit]
  unfold ons_pressure ons_freeEnergyIntegral
  push_cast
  rfl




theorem ons_pressure_analyticAt_noncritical {beta : ℝ}
    (hbeta : 0 < beta) (hcrit : beta ≠ ons_betaC) :
    AnalyticAt ℝ ons_pressure beta := by
  have hc := (ons_pressureComplex_analyticAt_noncritical hbeta hcrit).re_ofReal
  apply hc.congr
  filter_upwards [ons_noncriticalNeighborhood_mem_nhds hbeta hcrit] with b hb
  rw [ons_pressureComplex_ofReal hb.1
    (ons_noncriticalNeighborhood_ne_betaC hbeta hcrit hb)]
  simp






theorem ons_phase_regularity :
    (∀ beta : ℝ, 0 < beta → beta ≠ ons_betaC →
      AnalyticAt ℝ ons_pressure beta) ∧
    ContDiffAt ℝ 1 ons_pressure ons_betaC ∧
    HasDerivAt ons_pressure (Real.sqrt 2) ons_betaC ∧
    (∀ n : ℕ, -4 + (32 / 5 : ℝ) * (n : ℝ) ≤
      ∫ x in Real.exp (-(n : ℝ))..1,
        ∫ y in x..(2 * x),
          ons_logGIntBetaDeriv2 ons_betaC x y) ∧
    Filter.Tendsto
      (fun n : ℕ =>
        (∫ x in (-Real.pi)..(-Real.exp (-(n : ℝ))),
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y) +
          ∫ x in Real.exp (-(n : ℝ))..Real.pi,
            ∫ y in (-Real.pi)..Real.pi,
              ons_logGIntBetaDeriv2 ons_betaC x y)
      Filter.atTop Filter.atTop := by
  exact ⟨fun beta hbeta hcrit =>
      ons_pressure_analyticAt_noncritical hbeta hcrit,
    ons_pressure_contDiffAt_one_betaC,
    ons_hasDerivAt_pressure_betaC,
    ons_criticalSecond_wedgeCutoff_lower,
    ons_criticalSecond_fullCutoff_tendsto⟩

end StatMech.Onsager
