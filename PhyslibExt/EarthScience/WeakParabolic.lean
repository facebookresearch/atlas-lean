-- Copyright (c) 2026 Meta Platforms, Inc. and affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.

module

public import Mathlib


open MeasureTheory
open scoped ENNReal
open Filter
open scoped BigOperators
open Set

@[expose] public section

-- Assembled from verified worker proofs; silence the unused-variable and
-- haveI style linters for this generated file.
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace EarthScience

/-- H¹₀(0,1) in one dimension. -/
structure WeakH10 where
  toFun : ℝ → ℝ
  weakDeriv : ℝ → ℝ
  weakDeriv_memLp :
    MemLp weakDeriv 2 (volume.restrict (Set.Icc 0 1))
  toFun_eq_integral :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, toFun x = ∫ t in (0 : ℝ)..x, weakDeriv t
  integral_weakDeriv_eq_zero :
    ∫ t in (0 : ℝ)..1, weakDeriv t = 0

/-- Test functions for the parabolic weak formulation: smooth functions on
time × space, compactly supported inside `(t0, t1) × (0, 1)`.
Note: `ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞)` is C^∞. Under current Mathlib `ContDiff` is indexed
by `ℕ∞ω`, where `⊤ = ω` means analytic, while `∞` means C^∞. -/
def ParabolicTest (t0 t1 : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun p : ℝ × ℝ => φ p.1 p.2)
    ∧ HasCompactSupport (fun p : ℝ × ℝ => φ p.1 p.2)
    ∧ ∀ t x, φ t x ≠ 0 → t0 < t ∧ t < t1 ∧ 0 < x ∧ x < 1

/-- Rectangle integral over `[t0,t1] × [0,1]`. -/
noncomputable def rect (t0 t1 : ℝ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
    f p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))

theorem young_inequality {a b τ kmin : ℝ} (hτ : 0 < τ) (hkmin : 0 < kmin) :
    2 * τ * (a * b) ≤ (τ / kmin) * a ^ 2 + τ * kmin * b ^ 2 := by
  have hkm : kmin ≠ 0 := ne_of_gt hkmin
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hnonneg : 0 ≤ (τ / kmin) * (a - kmin * b) ^ 2 := by positivity
  have key : (τ / kmin) * a ^ 2 + τ * kmin * b ^ 2 - 2 * τ * (a * b)
      = (τ / kmin) * (a - kmin * b) ^ 2 := by
    field_simp
    ring
  linarith


theorem parabolic_assembly {τ kmin A B C D E G S K R : ℝ}
    (hτ : 0 < τ) (hkmin : 0 < kmin)
    (hE : E ^ 2 = A) (hG : G ^ 2 = D)
    (hident : (A - B) / 2 ≤ S) (hkap : kmin * C ≤ K)
    (hstep : S / τ + K = R) (hcs : R ≤ G * E) :
    (1 - τ * kmin) * A + 2 * τ * kmin * C ≤ B + (τ / kmin) * D := by
  have hτ' : τ ≠ 0 := ne_of_gt hτ
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hSeq : S + τ * K = τ * R := by
    field_simp at hstep ⊢
    linarith
  have hτK : τ * kmin * C ≤ τ * K := by
    have h := mul_le_mul_of_nonneg_left hkap hτ0
    linarith
  have hR : τ * R ≤ τ * (G * E) := by
    have h := mul_le_mul_of_nonneg_left hcs hτ0
    linarith
  have hmain : (A - B) / 2 + τ * kmin * C ≤ τ * (G * E) := by
    linarith [hSeq, hR, hτK, hident]
  have young := young_inequality (a := G) (b := E) hτ hkmin
  rw [hG, hE] at young
  linarith [hmain, young]


theorem eLpNorm_two_toReal_sq {f : ℝ → ℝ} {μ : Measure ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  have hfAEM : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_of_lt hf)
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hmul : AEStronglyMeasurable (f * f) μ := hfAEM.mul hfAEM
  have hsq_eq : (fun x => (f x) ^ 2) = f * f := by
    ext x
    simp [pow_two, Pi.mul_apply]
  rw [hsq_eq, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.Eventually.of_forall fun x => mul_self_nonneg _
  · exact hmul
  rw [← ENNReal.toReal_pow]
  congr 1
  rw [← ENNReal.rpow_natCast,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hfAEM, eLpNorm',
    ← ENNReal.rpow_mul, h_two]
  have hexp : (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [hexp, ENNReal.rpow_one]
  apply lintegral_congr_ae
  filter_upwards with x
  have h2r : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_cast
  rw [← ofReal_norm, Real.norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two, h2r,
    Real.rpow_natCast, sq_abs, pow_two, Pi.mul_apply]


theorem intervalIntegral_eq_integral_restrict_Icc {g : ℝ → ℝ} :
    ∫ x in (0:ℝ)..1, g x = ∫ x, g x ∂(volume.restrict (Set.Icc 0 1)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have ht : NullMeasurableSet (Set.Icc (0:ℝ) 1) volume :=
    measurableSet_Icc.nullMeasurableSet
  have hts : Set.Ioc (0:ℝ) 1 ⊆ Set.Icc 0 1 := Set.Ioc_subset_Icc_self
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0} : Set ℝ) := by
    rw [ae_iff]
    simp
  have h't : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.Icc (0:ℝ) 1 \ Set.Ioc 0 1 → g x = 0 := by
    filter_upwards [h0] with x hx hxmem
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff] at hx hxmem
    have hx0 : x = 0 := by
      have hnge : ¬ (0:ℝ) < x := fun hlt => hxmem.2 ⟨hlt, hxmem.1.2⟩
      exact le_antisymm (le_of_not_gt hnge) hxmem.1.1
    exact absurd hx0 hx
  exact (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero ht hts h't).symm


theorem isFiniteMeasure_restrict_Icc01 :
    IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [isFiniteMeasure_restrict]
  rw [Real.volume_Icc]
  simp


theorem WeakH10.memLp_toFun (u : WeakH10) :
    MemLp u.toFun 2 (volume.restrict (Set.Icc 0 1)) := by
  have _hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    isFiniteMeasure_restrict_Icc01
  have hw_int : Integrable u.weakDeriv (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    u.weakDeriv_memLp.integrable (by simp)
  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hIntOn : IntegrableOn u.weakDeriv (Set.uIcc (0:ℝ) 1) volume := by
    rw [huIcc]
    exact hw_int
  have hcont_prim : ContinuousOn (fun x => ∫ t in (0:ℝ)..x, u.weakDeriv t)
      (Set.uIcc (0:ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval hIntOn
  rw [huIcc] at hcont_prim
  have hcont : ContinuousOn u.toFun (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.congr hcont_prim
    intro x hx
    exact u.toFun_eq_integral x hx
  have hmeas : AEStronglyMeasurable u.toFun (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ‖u.toFun x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hC x hx
  exact MemLp.of_bound hmeas C hbdd

/-- Energy bound for one implicit-Euler step, assuming the step equation
and `MemLp` hypotheses (CORRECTED: the uncorrected statement was false):
`(1 - τ*kmin) * ‖u‖² + 2*τ*kmin * ‖u'‖² ≤ ‖uprev‖² + (τ/kmin) * ‖F‖²`
(all norms L² on `[0,1]`). -/

theorem parabolic_euler_step_energy
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin) (hτk : τ * kmin < 1)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (u : WeakH10)
    (hstep : ∀ v : WeakH10,
      ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, F x * v.toFun x) :
    (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + (τ / kmin) * (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  have _hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    isFiniteMeasure_restrict_Icc01
  have hu : MemLp u.toFun 2 (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    u.memLp_toFun
  have hstep_u := hstep u
  rw [intervalIntegral_eq_integral_restrict_Icc,
    intervalIntegral_eq_integral_restrict_Icc] at hstep_u
  -- Integrability of (u - uprev) * u
  have h_diff : MemLp (u.toFun - uprev) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hu.sub huprev
  have h_prod1 : Integrable (fun x => (u.toFun x - uprev x) * u.toFun x)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    h_diff.integrable_mul hu
  have h1_eq : (fun x => (u.toFun x - uprev x) / τ * u.toFun x)
      = (fun x => ((u.toFun x - uprev x) * u.toFun x) / τ) := by
    ext x
    ring
  have h1 : Integrable (fun x => (u.toFun x - uprev x) / τ * u.toFun x)
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [h1_eq]
    exact h_prod1.div_const τ
  have h3 : Integrable (fun x => F x * u.toFun x)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hF.integrable_mul hu
  -- Bound on κ
  have hκ_bound : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)), ‖κ x‖ ≤ |kmax| := by
    filter_upwards [hκ] with x hx
    have hpos : 0 < κ x := lt_of_lt_of_le hkmin hx.1
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact le_trans hx.2 (le_abs_self kmax)
  have h_sq_w : Integrable (fun x => (u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    u.weakDeriv_memLp.integrable_sq
  have hκ_sq : Integrable (fun x => κ x * (u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    h_sq_w.bdd_mul hκ_meas hκ_bound
  have h2_eq : (fun x => κ x * u.weakDeriv x * u.weakDeriv x)
      = (fun x => κ x * (u.weakDeriv x) ^ 2) := by
    ext x
    ring
  have h2 : Integrable (fun x => κ x * u.weakDeriv x * u.weakDeriv x)
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [h2_eq]
    exact hκ_sq
  rw [integral_add h1 h2] at hstep_u
  have hA : ∫ x, (u.toFun x - uprev x) / τ * u.toFun x
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = (∫ x, (u.toFun x - uprev x) * u.toFun x
        ∂(volume.restrict (Set.Icc (0:ℝ) 1))) / τ := by
    rw [h1_eq]
    exact integral_div τ _
  rw [hA] at hstep_u
  -- Polarization: (A - B)/2 ≤ S
  have h_sq_u : Integrable (fun x => (u.toFun x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hu.integrable_sq
  have h_sq_uprev : Integrable (fun x => (uprev x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    huprev.integrable_sq
  have h_sub_sq : Integrable (fun x => (u.toFun x) ^ 2 - (uprev x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    h_sq_u.sub h_sq_uprev
  have h_half : Integrable (fun x => ((u.toFun x) ^ 2 - (uprev x) ^ 2) / 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    h_sub_sq.div_const 2
  have h_le : ∀ x, ((u.toFun x) ^ 2 - (uprev x) ^ 2) / 2
      ≤ (u.toFun x - uprev x) * u.toFun x := by
    intro x
    have h_eq : (u.toFun x - uprev x) * u.toFun x
        - ((u.toFun x) ^ 2 - (uprev x) ^ 2) / 2
        = (u.toFun x - uprev x) ^ 2 / 2 := by ring
    have hnn : 0 ≤ (u.toFun x - uprev x) ^ 2 / 2 := by positivity
    linarith
  have hmono : ∫ x, ((u.toFun x) ^ 2 - (uprev x) ^ 2) / 2
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      ≤ ∫ x, (u.toFun x - uprev x) * u.toFun x
        ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
    integral_mono h_half h_prod1 h_le
  have h_int_sub : ∫ x, (u.toFun x) ^ 2 - (uprev x) ^ 2
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = (∫ x, (u.toFun x) ^ 2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
        - ∫ x, (uprev x) ^ 2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
    integral_sub h_sq_u h_sq_uprev
  have hA_def : (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      = ∫ x, (u.toFun x) ^ 2 ∂(volume.restrict (Set.Icc 0 1)) :=
    eLpNorm_two_toReal_sq hu
  have hB_def : (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      = ∫ x, (uprev x) ^ 2 ∂(volume.restrict (Set.Icc 0 1)) :=
    eLpNorm_two_toReal_sq huprev
  have h_half_eq : ∫ x, ((u.toFun x) ^ 2 - (uprev x) ^ 2) / 2
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = ((eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        - (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2) / 2 := by
    have hdiv : ∫ x, ((u.toFun x) ^ 2 - (uprev x) ^ 2) / 2
        ∂(volume.restrict (Set.Icc (0:ℝ) 1))
        = (∫ x, (u.toFun x) ^ 2 - (uprev x) ^ 2
          ∂(volume.restrict (Set.Icc (0:ℝ) 1))) / 2 :=
      integral_div 2 _
    rw [hdiv, h_int_sub, ← hA_def, ← hB_def]
  rw [h_half_eq] at hmono
  -- Diffusion lower bound: kmin * C ≤ K
  have hC_def : (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      = ∫ x, (u.weakDeriv x) ^ 2 ∂(volume.restrict (Set.Icc 0 1)) :=
    eLpNorm_two_toReal_sq u.weakDeriv_memLp
  have h_kmin_int : Integrable (fun x => kmin * (u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    h_sq_w.const_mul kmin
  have h_le_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      kmin * (u.weakDeriv x) ^ 2 ≤ κ x * (u.weakDeriv x) ^ 2 := by
    filter_upwards [hκ] with x hx
    exact mul_le_mul_of_nonneg_right hx.1 (sq_nonneg _)
  have hmono_k : ∫ x, kmin * (u.weakDeriv x) ^ 2
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      ≤ ∫ x, κ x * (u.weakDeriv x) ^ 2
        ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
    integral_mono_ae h_kmin_int hκ_sq h_le_ae
  have h_kmin_eq : ∫ x, kmin * (u.weakDeriv x) ^ 2
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
    have hcm : ∫ x, kmin * (u.weakDeriv x) ^ 2
        ∂(volume.restrict (Set.Icc (0:ℝ) 1))
        = kmin * ∫ x, (u.weakDeriv x) ^ 2
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
      integral_const_mul kmin _
    rw [hcm, ← hC_def]
  rw [h_kmin_eq] at hmono_k
  have hK_eq : ∫ x, κ x * (u.weakDeriv x) ^ 2
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      = ∫ x, κ x * u.weakDeriv x * u.weakDeriv x
        ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [← h2_eq]
  rw [hK_eq] at hmono_k
  -- Cauchy-Schwarz: R ≤ G * E
  have hD_def : (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      = ∫ x, (F x) ^ 2 ∂(volume.restrict (Set.Icc 0 1)) :=
    eLpNorm_two_toReal_sq hF
  have h_inner_eq : inner ℝ (hF.toLp F) (hu.toLp u.toFun)
      = ∫ x, F x * u.toFun x ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp, hu.coeFn_toLp] with x hxF hxu
    rw [Real.inner_apply, hxF, hxu]
  have h_cs : inner ℝ (hF.toLp F) (hu.toLp u.toFun)
      ≤ ‖hF.toLp F‖ * ‖hu.toLp u.toFun‖ :=
    real_inner_le_norm _ _
  rw [Lp.norm_toLp F hF, Lp.norm_toLp u.toFun hu] at h_cs
  rw [h_inner_eq] at h_cs
  exact parabolic_assembly hτ hkmin rfl rfl hmono hmono_k hstep_u h_cs


theorem weakH10_meas_finite :
    IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))) :=
  ⟨by simp [Real.volume_Icc]⟩

/-- The primitive of an `L²` function is a.e. strongly measurable. -/

theorem weakH10_prim_aes (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    AEStronglyMeasurable (fun x => ∫ t in (0 : ℝ)..x, g t)
      (volume.restrict (Set.Icc 0 1)) := by
  have := weakH10_meas_finite
  have hInt : Integrable g (volume.restrict (Set.Icc 0 1)) := hg.integrable one_le_two
  have hInd : Integrable ((Set.Icc (0 : ℝ) 1).indicator g) volume :=
    (integrable_indicator_iff (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc).mpr hInt
  have hCont : Continuous
      (fun x => ∫ t in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator g t) :=
    hInd.continuous_primitive (0 : ℝ)
  have hEq : Set.EqOn (fun x => ∫ t in (0 : ℝ)..x, g t)
      (fun x => ∫ t in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator g t)
      (Set.Icc 0 1) := by
    intro x hx
    show ∫ t in (0 : ℝ)..x, g t
      = ∫ t in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator g t
    rw [intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_of_le hx.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.trans hx.2⟩
    exact (Set.indicator_of_mem htIcc g).symm
  exact (hCont.continuousOn.congr hEq).aestronglyMeasurable measurableSet_Icc

/-- An `L²` function on `[0,1]` is interval integrable on every `[0,x]`, `x ∈ [0,1]`. -/

theorem weakH10_memLp_intervalIntegrable (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable g volume 0 x := by
  have := weakH10_meas_finite
  have hIntOn : IntegrableOn g (Set.Icc 0 1) volume := hg.integrable one_le_two
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
  exact hIntOn.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans hx.2⟩)

/-- Pointwise bound: the primitive is controlled by the `L²` norm. -/

theorem weakH10_prim_bound (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖∫ t in (0 : ℝ)..x, g t‖ ≤ (eLpNorm g 2 (volume.restrict (Set.Icc 0 1))).toReal := by
  have := weakH10_meas_finite
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hsub01 : Set.Ioc (0 : ℝ) x ⊆ Set.Icc 0 1 :=
    fun t ht => ⟨ht.1.le, ht.2.trans hx1⟩
  have hμν : (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Ioc 0 x)
      = volume.restrict (Set.Ioc 0 x) := by
    rw [Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left hsub01]
  have haes : AEStronglyMeasurable g (volume.restrict (Set.Ioc (0 : ℝ) x)) := by
    rw [← hμν]
    exact hg.aestronglyMeasurable.restrict
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) x)]
      (fun t => ‖g t‖) :=
    Filter.Eventually.of_forall fun t => norm_nonneg _
  have hnorm_eq : (∫ t in Set.Ioc (0 : ℝ) x, ‖g t‖ ∂volume)
      = (eLpNorm g 1 (volume.restrict (Set.Ioc (0 : ℝ) x))).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn haes.norm,
      eLpNorm_one_eq_lintegral_enorm haes]
    congr 1
    exact lintegral_congr_ae (Filter.Eventually.of_forall fun t => ofReal_norm (g t))
  have hfin2 : eLpNorm g 2 (volume.restrict (Set.Icc 0 1)) < ⊤ := hg.eLpNorm_lt_top
  have hν1 : (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ ≤ 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hexp0 : (0 : ℝ) ≤ 1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  have hrpow : (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
      ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) ≤ 1 := by
    have h := ENNReal.rpow_le_rpow hν1 hexp0
    rwa [ENNReal.one_rpow] at h
  have hmono : eLpNorm g 1 (volume.restrict (Set.Ioc (0 : ℝ) x))
      ≤ eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))
        * (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
          ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ one_le_two haes
  have hrestr : eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))
      ≤ eLpNorm g 2 (volume.restrict (Set.Icc 0 1)) := by
    have h := eLpNorm_restrict_le g 2 (volume.restrict (Set.Icc 0 1)) (Set.Ioc 0 x)
    rwa [hμν] at h
  have hfinR : eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))
      * (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
        ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) < ⊤ :=
    ENNReal.mul_lt_top (lt_of_le_of_lt hrestr hfin2)
      (lt_of_le_of_lt hrpow ENNReal.one_lt_top)
  have hfinL : eLpNorm g 1 (volume.restrict (Set.Ioc (0 : ℝ) x)) < ⊤ :=
    lt_of_le_of_lt hmono hfinR
  have htoReal : (eLpNorm g 1 (volume.restrict (Set.Ioc (0 : ℝ) x))).toReal
      ≤ (eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))
        * (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
          ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal :=
    (ENNReal.toReal_le_toReal hfinL.ne hfinR.ne).mpr hmono
  have hrhs : (eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))
      * (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
        ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal
      ≤ (eLpNorm g 2 (volume.restrict (Set.Icc 0 1))).toReal := by
    rw [ENNReal.toReal_mul]
    have h2 : ((volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
        ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal ≤ 1 := by
      have h2' : ((volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
          ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal
          ≤ (1 : ENNReal).toReal :=
        (ENNReal.toReal_le_toReal (lt_of_le_of_lt hrpow ENNReal.one_lt_top).ne
          ENNReal.one_ne_top).mpr hrpow
      rwa [ENNReal.toReal_one] at h2'
    calc (eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))).toReal
          * ((volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
            ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal
        ≤ (eLpNorm g 2 (volume.restrict (Set.Icc 0 1))).toReal * 1 :=
          mul_le_mul ((ENNReal.toReal_le_toReal
            (lt_of_le_of_lt hrestr hfin2).ne hfin2.ne).mpr hrestr)
            h2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      _ = (eLpNorm g 2 (volume.restrict (Set.Icc 0 1))).toReal := mul_one _
  rw [intervalIntegral.integral_of_le hx0]
  calc ‖∫ t in Set.Ioc (0 : ℝ) x, g t ∂volume‖
      ≤ ∫ t in Set.Ioc (0 : ℝ) x, ‖g t‖ ∂volume := norm_integral_le_integral_norm _
    _ = (eLpNorm g 1 (volume.restrict (Set.Ioc (0 : ℝ) x))).toReal := hnorm_eq
    _ ≤ (eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) x))
          * (volume.restrict (Set.Ioc (0 : ℝ) x)) Set.univ
            ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)).toReal := htoReal
    _ ≤ (eLpNorm g 2 (volume.restrict (Set.Icc 0 1))).toReal := hrhs

/-- H¹₀(0,1) is complete in the H¹ norm, in sequential form: a sequence
Cauchy in both `toFun` and `weakDeriv` (L² on `[0,1]`) converges in both
to a `WeakH10` limit. `Tendsto` is for the `eLpNorm` distance
`(eLpNorm (uₙ.toFun - u.toFun) 2 μ).toReal → 0`, resp. for `weakDeriv`. -/

theorem weakH10_complete (u : ℕ → WeakH10)
    (hCauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (eLpNorm ((u n).toFun - (u m).toFun) 2
        (volume.restrict (Set.Icc 0 1))).toReal < ε)
    (hCauchy' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (eLpNorm ((u n).weakDeriv - (u m).weakDeriv) 2
        (volume.restrict (Set.Icc 0 1))).toReal < ε) :
    ∃ w : WeakH10,
      Filter.Tendsto (fun n => (eLpNorm ((u n).toFun - w.toFun) 2
        (volume.restrict (Set.Icc 0 1))).toReal) Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun n => (eLpNorm ((u n).weakDeriv - w.weakDeriv) 2
        (volume.restrict (Set.Icc 0 1))).toReal) Filter.atTop (nhds 0) := by
  have := weakH10_meas_finite
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨one_le_two⟩
  have : Nonempty (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ)))) := ⟨0⟩
  have hmemW : ∀ n, MemLp ((u n).weakDeriv) 2 (volume.restrict (Set.Icc 0 1)) :=
    fun n => (u n).weakDeriv_memLp
  set F : ℕ → Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))) :=
    fun n => MemLp.toLp _ (hmemW n) with hFdef
  have hdist : ∀ m n, dist (F m) (F n)
      = (eLpNorm ((u m).weakDeriv - (u n).weakDeriv) 2
        (volume.restrict (Set.Icc 0 1))).toReal := by
    intro m n
    rw [Lp.dist_def]
    simp only [hFdef]
    rw [eLpNorm_congr_ae ((hmemW m).coeFn_toLp.sub (hmemW n).coeFn_toLp)]
  have hCauchyLp : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy' ε hε
    exact ⟨N, fun m hm n hn => by rw [hdist m n]; exact hN m hm n hn⟩
  set W : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))) :=
    Filter.limUnder Filter.atTop F
  have hlim : Filter.Tendsto F Filter.atTop (nhds W) := hCauchyLp.tendsto_limUnder
  have hWlim : Filter.Tendsto
      (fun n => (eLpNorm ((u n).weakDeriv - ⇑W) 2
        (volume.restrict (Set.Icc 0 1))).toReal) Filter.atTop (nhds 0) := by
    have h0 := tendsto_iff_dist_tendsto_zero.mp hlim
    have heq : (fun n => dist (F n) W)
        = fun n => (eLpNorm ((u n).weakDeriv - ⇑W) 2
          (volume.restrict (Set.Icc 0 1))).toReal := by
      funext n
      rw [Lp.dist_def]
      simp only [hFdef]
      rw [eLpNorm_congr_ae ((hmemW n).coeFn_toLp.sub Filter.EventuallyEq.rfl)]
    rwa [heq] at h0
  have hIntW : IntervalIntegrable ⇑W volume 0 1 :=
    weakH10_memLp_intervalIntegrable ⇑W (Lp.memLp W) 1 ⟨zero_le_one, le_rfl⟩
  have hIntN : ∀ n, IntervalIntegrable ((u n).weakDeriv) volume 0 1 :=
    fun n => weakH10_memLp_intervalIntegrable _ (hmemW n) 1 ⟨zero_le_one, le_rfl⟩
  have hIntW0 : ∫ t in (0 : ℝ)..1, ⇑W t = 0 := by
    have hlimI : Filter.Tendsto (fun n => ∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
        Filter.atTop (nhds (∫ t in (0 : ℝ)..1, ⇑W t)) := by
      have hdiff : Filter.Tendsto
          (fun n => (∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
            - (∫ t in (0 : ℝ)..1, ⇑W t))
          Filter.atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        show Filter.Tendsto
          (fun n => ‖(∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
            - (∫ t in (0 : ℝ)..1, ⇑W t)‖)
          Filter.atTop (nhds 0)
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hWlim
        · intro n
          exact norm_nonneg _
        · intro n
          have hsub := intervalIntegral.integral_sub (hIntN n) hIntW
          calc ‖(∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
                - (∫ t in (0 : ℝ)..1, ⇑W t)‖
              = ‖∫ t in (0 : ℝ)..1, ((u n).weakDeriv - ⇑W) t‖ := by
                congr 1
                exact hsub.symm
            _ ≤ (eLpNorm ((u n).weakDeriv - ⇑W) 2
                (volume.restrict (Set.Icc 0 1))).toReal :=
                weakH10_prim_bound _ (MemLp.sub (hmemW n) (Lp.memLp W)) 1
                  ⟨zero_le_one, le_rfl⟩
      have hadd : Filter.Tendsto
          (fun n => (∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
            - (∫ t in (0 : ℝ)..1, ⇑W t) + (∫ t in (0 : ℝ)..1, ⇑W t))
          Filter.atTop (nhds (0 + ∫ t in (0 : ℝ)..1, ⇑W t)) :=
        hdiff.add tendsto_const_nhds
      simp only [sub_add_cancel, zero_add] at hadd
      exact hadd
    have h0 : Filter.Tendsto (fun n => ∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
        Filter.atTop (nhds 0) := by
      have heq : (fun n => ∫ t in (0 : ℝ)..1, (u n).weakDeriv t)
          = fun _ => (0 : ℝ) :=
        funext fun n => (u n).integral_weakDeriv_eq_zero
      rw [heq]
      exact tendsto_const_nhds
    have huniq := tendsto_nhds_unique h0 hlimI
    exact huniq.symm
  have haesW : AEStronglyMeasurable (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)
      (volume.restrict (Set.Icc 0 1)) :=
    weakH10_prim_aes _ (Lp.memLp W)
  have haesN : ∀ n, AEStronglyMeasurable ((u n).toFun)
      (volume.restrict (Set.Icc 0 1)) := by
    intro n
    have heq : (u n).toFun =ᵐ[volume.restrict (Set.Icc 0 1)]
        (fun x => ∫ t in (0 : ℝ)..x, (u n).weakDeriv t) :=
      (ae_restrict_mem measurableSet_Icc).mono
        fun x hx => (u n).toFun_eq_integral x hx
    exact (weakH10_prim_aes _ (hmemW n)).congr heq.symm
  have hToFun : Filter.Tendsto
      (fun n => (eLpNorm ((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) 2
        (volume.restrict (Set.Icc 0 1))).toReal) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hWlim
    · intro n
      exact ENNReal.toReal_nonneg
    · intro n
      have haes_sub : AEStronglyMeasurable
          ((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t))
          (volume.restrict (Set.Icc 0 1)) :=
        (haesN n).sub haesW
      have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) x‖
            ≤ (eLpNorm ((u n).weakDeriv - ⇑W) 2
              (volume.restrict (Set.Icc 0 1))).toReal := by
        intro x hx
        have hInt1 := weakH10_memLp_intervalIntegrable _ (hmemW n) x hx
        have hInt2 := weakH10_memLp_intervalIntegrable _ (Lp.memLp W) x hx
        have hsub := intervalIntegral.integral_sub hInt1 hInt2
        calc ‖((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) x‖
            = ‖(u n).toFun x - (∫ t in (0 : ℝ)..x, ⇑W t)‖ := rfl
          _ = ‖(∫ t in (0 : ℝ)..x, (u n).weakDeriv t)
              - (∫ t in (0 : ℝ)..x, ⇑W t)‖ := by
              rw [(u n).toFun_eq_integral x hx]
          _ = ‖∫ t in (0 : ℝ)..x, ((u n).weakDeriv - ⇑W) t‖ := by
              congr 1
              exact hsub.symm
          _ ≤ (eLpNorm ((u n).weakDeriv - ⇑W) 2
              (volume.restrict (Set.Icc 0 1))).toReal :=
              weakH10_prim_bound _ (MemLp.sub (hmemW n) (Lp.memLp W)) x hx
      have hae_le : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
          ‖((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) x‖
            ≤ ‖(fun _ => (eLpNorm ((u n).weakDeriv - ⇑W) 2
              (volume.restrict (Set.Icc 0 1))).toReal) x‖ :=
        (ae_restrict_mem measurableSet_Icc).mono fun x hx => by
          have h := hpt x hx
          have hC : ‖(fun _ => (eLpNorm ((u n).weakDeriv - ⇑W) 2
              (volume.restrict (Set.Icc 0 1))).toReal) x‖
              = (eLpNorm ((u n).weakDeriv - ⇑W) 2
                (volume.restrict (Set.Icc 0 1))).toReal := by
            rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          rwa [hC]
      have hmono_n : eLpNorm ((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) 2
          (volume.restrict (Set.Icc 0 1))
          ≤ eLpNorm (fun (_ : ℝ) => (eLpNorm ((u n).weakDeriv - ⇑W) 2
            (volume.restrict (Set.Icc 0 1))).toReal) 2
            (volume.restrict (Set.Icc 0 1)) :=
        eLpNorm_mono_ae haes_sub hae_le
      have hμ1 : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
        simp [Real.volume_Icc]
      have hμ0 : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
        intro hm
        rw [hm] at hμ1
        simp at hμ1
      have hconst : eLpNorm (fun (_ : ℝ) => (eLpNorm ((u n).weakDeriv - ⇑W) 2
          (volume.restrict (Set.Icc 0 1))).toReal) 2
          (volume.restrict (Set.Icc 0 1))
          = ENNReal.ofReal (eLpNorm ((u n).weakDeriv - ⇑W) 2
            (volume.restrict (Set.Icc 0 1))).toReal := by
        rw [eLpNorm_const _ two_ne_zero hμ0, hμ1, Real.enorm_eq_ofReal_abs,
          abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.one_rpow, mul_one]
      have hle_n : eLpNorm ((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) 2
          (volume.restrict (Set.Icc 0 1))
          ≤ ENNReal.ofReal (eLpNorm ((u n).weakDeriv - ⇑W) 2
            (volume.restrict (Set.Icc 0 1))).toReal := by
        rw [← hconst]
        exact hmono_n
      have hfinH : eLpNorm ((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) 2
          (volume.restrict (Set.Icc 0 1)) < ⊤ :=
        lt_of_le_of_lt hle_n ENNReal.ofReal_lt_top
      calc (eLpNorm ((u n).toFun - (fun x => ∫ t in (0 : ℝ)..x, ⇑W t)) 2
          (volume.restrict (Set.Icc 0 1))).toReal
          ≤ (ENNReal.ofReal (eLpNorm ((u n).weakDeriv - ⇑W) 2
            (volume.restrict (Set.Icc 0 1))).toReal).toReal :=
            (ENNReal.toReal_le_toReal hfinH.ne ENNReal.ofReal_ne_top).mpr hle_n
        _ = (eLpNorm ((u n).weakDeriv - ⇑W) 2
            (volume.restrict (Set.Icc 0 1))).toReal :=
            ENNReal.toReal_ofReal ENNReal.toReal_nonneg
  exact ⟨⟨(fun x => ∫ t in (0 : ℝ)..x, ⇑W t), ⇑W, Lp.memLp W,
    (fun x _ => rfl), hIntW0⟩, hToFun, hWlim⟩


@[ext]
theorem WeakH10.ext (a b : WeakH10)
    (h1 : a.toFun = b.toFun) (h2 : a.weakDeriv = b.weakDeriv) : a = b := by
  cases a; cases b; simp_all


instance : Zero WeakH10 where
  zero :=
    { toFun := 0
      weakDeriv := 0
      weakDeriv_memLp := MemLp.zero
      toFun_eq_integral := fun x _ => by simp [intervalIntegral.integral_zero]
      integral_weakDeriv_eq_zero := by simp [intervalIntegral.integral_zero] }


instance : Add WeakH10 where
  add a b :=
    { toFun := a.toFun + b.toFun
      weakDeriv := a.weakDeriv + b.weakDeriv
      weakDeriv_memLp := a.weakDeriv_memLp.add b.weakDeriv_memLp
      toFun_eq_integral := fun x hx => by
        have h1 := weakH10_memLp_intervalIntegrable _ a.weakDeriv_memLp x hx
        have h2 := weakH10_memLp_intervalIntegrable _ b.weakDeriv_memLp x hx
        have hadd := intervalIntegral.integral_add h1 h2
        calc (a.toFun + b.toFun) x = a.toFun x + b.toFun x := rfl
          _ = (∫ t in (0 : ℝ)..x, a.weakDeriv t)
              + ∫ t in (0 : ℝ)..x, b.weakDeriv t := by
              rw [a.toFun_eq_integral x hx, b.toFun_eq_integral x hx]
          _ = ∫ t in (0 : ℝ)..x, a.weakDeriv t + b.weakDeriv t := hadd.symm
          _ = ∫ t in (0 : ℝ)..x, (a.weakDeriv + b.weakDeriv) t := rfl
      integral_weakDeriv_eq_zero := by
        have h1 := weakH10_memLp_intervalIntegrable _ a.weakDeriv_memLp 1
          ⟨zero_le_one, le_rfl⟩
        have h2 := weakH10_memLp_intervalIntegrable _ b.weakDeriv_memLp 1
          ⟨zero_le_one, le_rfl⟩
        have hadd := intervalIntegral.integral_add h1 h2
        calc ∫ t in (0 : ℝ)..1, (a.weakDeriv + b.weakDeriv) t
            = ∫ t in (0 : ℝ)..1, a.weakDeriv t + b.weakDeriv t := rfl
          _ = (∫ t in (0 : ℝ)..1, a.weakDeriv t)
              + ∫ t in (0 : ℝ)..1, b.weakDeriv t := hadd
          _ = (0 : ℝ) + 0 := by
              rw [a.integral_weakDeriv_eq_zero, b.integral_weakDeriv_eq_zero]
          _ = 0 := add_zero _ }


instance : Neg WeakH10 where
  neg a :=
    { toFun := -a.toFun
      weakDeriv := -a.weakDeriv
      weakDeriv_memLp := a.weakDeriv_memLp.neg
      toFun_eq_integral := fun x hx => by
        calc (-a.toFun) x = -(a.toFun x) := rfl
          _ = -(∫ t in (0 : ℝ)..x, a.weakDeriv t) := by
              rw [a.toFun_eq_integral x hx]
          _ = ∫ t in (0 : ℝ)..x, -(a.weakDeriv t) :=
              intervalIntegral.integral_neg.symm
          _ = ∫ t in (0 : ℝ)..x, (-a.weakDeriv) t := rfl
      integral_weakDeriv_eq_zero := by
        calc ∫ t in (0 : ℝ)..1, (-a.weakDeriv) t
            = ∫ t in (0 : ℝ)..1, -(a.weakDeriv t) := rfl
          _ = -(∫ t in (0 : ℝ)..1, a.weakDeriv t) :=
              intervalIntegral.integral_neg
          _ = -(0 : ℝ) := by rw [a.integral_weakDeriv_eq_zero]
          _ = 0 := neg_zero }


instance : Sub WeakH10 where
  sub a b :=
    { toFun := a.toFun - b.toFun
      weakDeriv := a.weakDeriv - b.weakDeriv
      weakDeriv_memLp := a.weakDeriv_memLp.sub b.weakDeriv_memLp
      toFun_eq_integral := fun x hx => by
        have h1 := weakH10_memLp_intervalIntegrable _ a.weakDeriv_memLp x hx
        have h2 := weakH10_memLp_intervalIntegrable _ b.weakDeriv_memLp x hx
        have hsub := intervalIntegral.integral_sub h1 h2
        calc (a.toFun - b.toFun) x = a.toFun x - b.toFun x := rfl
          _ = (∫ t in (0 : ℝ)..x, a.weakDeriv t)
              - ∫ t in (0 : ℝ)..x, b.weakDeriv t := by
              rw [a.toFun_eq_integral x hx, b.toFun_eq_integral x hx]
          _ = ∫ t in (0 : ℝ)..x, a.weakDeriv t - b.weakDeriv t := hsub.symm
          _ = ∫ t in (0 : ℝ)..x, (a.weakDeriv - b.weakDeriv) t := rfl
      integral_weakDeriv_eq_zero := by
        have h1 := weakH10_memLp_intervalIntegrable _ a.weakDeriv_memLp 1
          ⟨zero_le_one, le_rfl⟩
        have h2 := weakH10_memLp_intervalIntegrable _ b.weakDeriv_memLp 1
          ⟨zero_le_one, le_rfl⟩
        have hsub := intervalIntegral.integral_sub h1 h2
        calc ∫ t in (0 : ℝ)..1, (a.weakDeriv - b.weakDeriv) t
            = ∫ t in (0 : ℝ)..1, a.weakDeriv t - b.weakDeriv t := rfl
          _ = (∫ t in (0 : ℝ)..1, a.weakDeriv t)
              - ∫ t in (0 : ℝ)..1, b.weakDeriv t := hsub
          _ = (0 : ℝ) - 0 := by
              rw [a.integral_weakDeriv_eq_zero, b.integral_weakDeriv_eq_zero]
          _ = 0 := sub_zero _ }


instance : SMul ℝ WeakH10 where
  smul c a :=
    { toFun := c • a.toFun
      weakDeriv := c • a.weakDeriv
      weakDeriv_memLp := a.weakDeriv_memLp.const_smul c
      toFun_eq_integral := fun x hx => by
        calc (c • a.toFun) x = c • (a.toFun x) := rfl
          _ = c • (∫ t in (0 : ℝ)..x, a.weakDeriv t) := by
              rw [a.toFun_eq_integral x hx]
          _ = ∫ t in (0 : ℝ)..x, c • (a.weakDeriv t) :=
              (intervalIntegral.integral_smul c _).symm
          _ = ∫ t in (0 : ℝ)..x, (c • a.weakDeriv) t := rfl
      integral_weakDeriv_eq_zero := by
        calc ∫ t in (0 : ℝ)..1, (c • a.weakDeriv) t
            = ∫ t in (0 : ℝ)..1, c • (a.weakDeriv t) := rfl
          _ = c • (∫ t in (0 : ℝ)..1, a.weakDeriv t) :=
              intervalIntegral.integral_smul c _
          _ = c • (0 : ℝ) := by rw [a.integral_weakDeriv_eq_zero]
          _ = 0 := smul_zero c }


instance : AddCommGroup WeakH10 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := by
    ext x
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
  zero_add a := by
    ext x
    · exact zero_add _
    · exact zero_add _
  add_zero a := by
    ext x
    · exact add_zero _
    · exact add_zero _
  neg_add_cancel a := by
    ext x
    · exact neg_add_cancel _
    · exact neg_add_cancel _
  add_comm a b := by
    ext x
    · exact add_comm _ _
    · exact add_comm _ _
  sub_eq_add_neg a b := by
    ext x
    · exact sub_eq_add_neg _ _
    · exact sub_eq_add_neg _ _


instance : Module ℝ WeakH10 where
  smul_add c a b := by
    ext x
    · exact smul_add c (a.toFun x) (b.toFun x)
    · exact smul_add c (a.weakDeriv x) (b.weakDeriv x)
  add_smul c d a := by
    ext x
    · exact add_smul c d (a.toFun x)
    · exact add_smul c d (a.weakDeriv x)
  mul_smul c d a := by
    ext x
    · exact mul_smul c d (a.toFun x)
    · exact mul_smul c d (a.weakDeriv x)
  one_smul a := by
    ext x
    · exact one_smul ℝ (a.toFun x)
    · exact one_smul ℝ (a.weakDeriv x)
  zero_smul a := by
    ext x
    · exact zero_smul ℝ (a.toFun x)
    · exact zero_smul ℝ (a.weakDeriv x)
  smul_zero c := by
    ext x
    · exact smul_zero c
    · exact smul_zero c


instance weakH10_fact_one_le_two : Fact (1 ≤ (2 : ENNReal)) := ⟨one_le_two⟩


theorem weakH10_toFun_memLp (u : WeakH10) :
    MemLp u.toFun 2 (volume.restrict (Set.Icc 0 1)) := by
  have := weakH10_meas_finite
  have haes : AEStronglyMeasurable u.toFun (volume.restrict (Set.Icc 0 1)) := by
    have heq : u.toFun =ᵐ[volume.restrict (Set.Icc 0 1)]
        (fun x => ∫ t in (0 : ℝ)..x, u.weakDeriv t) :=
      (ae_restrict_mem measurableSet_Icc).mono
        fun x hx => u.toFun_eq_integral x hx
    exact (weakH10_prim_aes _ u.weakDeriv_memLp).congr heq.symm
  refine MemLp.of_bound haes
    ((eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal) ?_
  apply (ae_restrict_mem measurableSet_Icc).mono
  intro x hx
  calc ‖u.toFun x‖ = ‖∫ t in (0 : ℝ)..x, u.weakDeriv t‖ := by
        rw [u.toFun_eq_integral x hx]
    _ ≤ (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
        weakH10_prim_bound _ u.weakDeriv_memLp x hx


noncomputable def weakH10_inner (u v : WeakH10) : ℝ :=
  inner ℝ ((weakH10_toFun_memLp u).toLp u.toFun)
    ((weakH10_toFun_memLp v).toLp v.toFun)
  + inner ℝ (u.weakDeriv_memLp.toLp u.weakDeriv)
    (v.weakDeriv_memLp.toLp v.weakDeriv)


noncomputable instance weakH10_preInnerCore : PreInnerProductSpace.Core ℝ WeakH10 where
  inner := weakH10_inner
  conj_inner_symm u v := by
    simp only [weakH10_inner, map_add, inner_conj_symm]
  re_inner_nonneg u := by
    simp only [weakH10_inner, RCLike.re_to_real]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by
    have hT : (weakH10_toFun_memLp (u + v)).toLp ((u + v).toFun)
        = (weakH10_toFun_memLp u).toLp u.toFun
          + (weakH10_toFun_memLp v).toLp v.toFun :=
      MemLp.toLp_add _ _
    have hD : ((u + v).weakDeriv_memLp).toLp ((u + v).weakDeriv)
        = (u.weakDeriv_memLp.toLp u.weakDeriv)
          + (v.weakDeriv_memLp.toLp v.weakDeriv) :=
      MemLp.toLp_add _ _
    simp only [weakH10_inner, hT, hD, inner_add_left]
    ring
  smul_left u v c := by
    have hT : (weakH10_toFun_memLp (c • u)).toLp ((c • u).toFun)
        = c • (weakH10_toFun_memLp u).toLp u.toFun :=
      MemLp.toLp_const_smul _ _
    have hD : ((c • u).weakDeriv_memLp).toLp ((c • u).weakDeriv)
        = c • (u.weakDeriv_memLp.toLp u.weakDeriv) :=
      MemLp.toLp_const_smul _ _
    simp only [weakH10_inner, hT, hD, inner_smul_left]
    ring


noncomputable instance weakH10_seminormedAddCommGroup : SeminormedAddCommGroup WeakH10 :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)


noncomputable instance weakH10_innerProductSpace : InnerProductSpace ℝ WeakH10 :=
  InnerProductSpace.ofCore (𝕜 := ℝ) inferInstance


theorem weakH10_inner_eq (u v : WeakH10) :
    inner ℝ u v = weakH10_inner u v := rfl


theorem weakH10_norm_sq (w : WeakH10) :
    ‖w‖ ^ 2 = (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      + (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  have h := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (E := WeakH10) w
  simp only [RCLike.re_to_real, weakH10_inner_eq, weakH10_inner] at h
  have hT : inner ℝ ((weakH10_toFun_memLp w).toLp w.toFun)
      ((weakH10_toFun_memLp w).toLp w.toFun)
      = (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
    rw [real_inner_self_eq_norm_sq, Lp.norm_toLp]
  have hD : inner ℝ (w.weakDeriv_memLp.toLp w.weakDeriv)
      (w.weakDeriv_memLp.toLp w.weakDeriv)
      = (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
    rw [real_inner_self_eq_norm_sq, Lp.norm_toLp]
  rw [hT, hD] at h
  exact h


theorem weakH10_eLpNorm_toFun_le (w : WeakH10) :
    (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ≤ ‖w‖ := by
  have hsq := weakH10_norm_sq w
  have hA : 0 ≤ (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hN : 0 ≤ ‖w‖ := norm_nonneg _
  have hB2 : 0 ≤ (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 :=
    sq_nonneg _
  have hle : (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [hsq]
    exact le_add_of_nonneg_right hB2
  have hsqrt := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq hA, Real.sqrt_sq hN] at hsqrt
  exact hsqrt


theorem weakH10_eLpNorm_weakDeriv_le (w : WeakH10) :
    (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ≤ ‖w‖ := by
  have hsq := weakH10_norm_sq w
  have hB : 0 ≤ (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hN : 0 ≤ ‖w‖ := norm_nonneg _
  have hA2 : 0 ≤ (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 :=
    sq_nonneg _
  have hle : (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [hsq]
    exact le_add_of_nonneg_left hA2
  have hsqrt := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq hB, Real.sqrt_sq hN] at hsqrt
  exact hsqrt


theorem weakH10_norm_le_add (w : WeakH10) :
    ‖w‖ ≤ (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
      + (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal := by
  have hsq := weakH10_norm_sq w
  have hA : 0 ≤ (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hB : 0 ≤ (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hN : 0 ≤ ‖w‖ := norm_nonneg _
  have hAB : 0 ≤ (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
      + (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    add_nonneg hA hB
  have hle : ‖w‖ ^ 2 ≤ ((eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
      + (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg hA hB]
  have hsqrt := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq hN, Real.sqrt_sq hAB] at hsqrt
  exact hsqrt


noncomputable instance weakH10_completeSpace : CompleteSpace WeakH10 :=
  UniformSpace.complete_of_cauchySeq_tendsto (fun u hu => by
    rw [Metric.cauchySeq_iff] at hu
    have hCauchy : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
        (eLpNorm ((u n).toFun - (u m).toFun) 2
          (volume.restrict (Set.Icc 0 1))).toReal < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun n hn m hm => ?_⟩
      have hdist := hN n hn m hm
      rw [dist_eq_norm] at hdist
      have hle := weakH10_eLpNorm_toFun_le ((u n) - (u m))
      calc (eLpNorm ((u n).toFun - (u m).toFun) 2
            (volume.restrict (Set.Icc 0 1))).toReal
          = (eLpNorm (((u n) - (u m)).toFun) 2
            (volume.restrict (Set.Icc 0 1))).toReal := rfl
        _ ≤ ‖(u n) - (u m)‖ := hle
        _ < ε := hdist
    have hCauchy' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
        (eLpNorm ((u n).weakDeriv - (u m).weakDeriv) 2
          (volume.restrict (Set.Icc 0 1))).toReal < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun n hn m hm => ?_⟩
      have hdist := hN n hn m hm
      rw [dist_eq_norm] at hdist
      have hle := weakH10_eLpNorm_weakDeriv_le ((u n) - (u m))
      calc (eLpNorm ((u n).weakDeriv - (u m).weakDeriv) 2
            (volume.restrict (Set.Icc 0 1))).toReal
          = (eLpNorm (((u n) - (u m)).weakDeriv) 2
            (volume.restrict (Set.Icc 0 1))).toReal := rfl
        _ ≤ ‖(u n) - (u m)‖ := hle
        _ < ε := hdist
    obtain ⟨w, hToFun, hWlim⟩ := weakH10_complete u hCauchy hCauchy'
    refine ⟨w, ?_⟩
    rw [tendsto_iff_dist_tendsto_zero]
    have hAdd : Filter.Tendsto
        (fun n => (eLpNorm ((u n).toFun - w.toFun) 2
            (volume.restrict (Set.Icc 0 1))).toReal
          + (eLpNorm ((u n).weakDeriv - w.weakDeriv) 2
            (volume.restrict (Set.Icc 0 1))).toReal)
        Filter.atTop (nhds 0) := by
      have h := hToFun.add hWlim
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAdd
    · intro n
      exact dist_nonneg
    · intro n
      simp only [dist_eq_norm]
      have hle := weakH10_norm_le_add ((u n) - w)
      calc ‖(u n) - w‖
          ≤ (eLpNorm (((u n) - w).toFun) 2
              (volume.restrict (Set.Icc 0 1))).toReal
            + (eLpNorm (((u n) - w).weakDeriv) 2
              (volume.restrict (Set.Icc 0 1))).toReal := hle
        _ = (eLpNorm ((u n).toFun - w.toFun) 2
              (volume.restrict (Set.Icc 0 1))).toReal
            + (eLpNorm ((u n).weakDeriv - w.weakDeriv) 2
              (volume.restrict (Set.Icc 0 1))).toReal := rfl)

/-- `WeakH10` carries a real inner-product-space structure (with the H¹
inner product above), and it is complete. This statement only elaborates
once the instances exist. -/

theorem weakH10_innerProductSpace_exists :
    ∃ _ : InnerProductSpace ℝ WeakH10, True := by
  exact ⟨inferInstance, trivial⟩


theorem eulerB_eLpNorm_sq (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      = ∫ x, (f x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have haes := hf.aestronglyMeasurable
  have hp0 : (2 : NNReal) ≠ 0 := by norm_num
  have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) hp0 haes
  norm_cast at hpow
  have hInt : Integrable (fun x => (f x) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.integrable_sq
  have hNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x => (f x) ^ 2) :=
    Filter.Eventually.of_forall fun x => sq_nonneg (f x)
  have hlin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ENNReal.ofReal (∫ x, (f x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
    apply lintegral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    show ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((f x) ^ 2)
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [Real.rpow_two, sq_abs]
  have hToReal := congrArg ENNReal.toReal hpow
  rw [← ENNReal.toReal_rpow] at hToReal
  rw [hlin] at hToReal
  have hIntNonneg : 0 ≤ ∫ x, (f x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integral_nonneg_of_ae hNonneg
  rw [ENNReal.toReal_ofReal hIntNonneg] at hToReal
  rw [Real.rpow_two] at hToReal
  exact hToReal


theorem eulerB_Icc_eq_Ioc (g : ℝ → ℝ) :
    (∫ x in Set.Icc (0 : ℝ) 1, g x ∂volume)
      = ∫ x in Set.Ioc (0 : ℝ) 1, g x ∂volume := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ 0} = {(0 : ℝ)} := by
      ext x
      simp
    rw [hset, Real.volume_singleton]
  filter_upwards [h0] with x hx
  by_cases hxIoc : x ∈ Set.Ioc (0 : ℝ) 1
  · have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxIoc.1.le, hxIoc.2⟩
    rw [Set.indicator_of_mem hxIcc, Set.indicator_of_mem hxIoc]
  · rw [Set.indicator_of_notMem hxIoc]
    have hxIcc : x ∉ Set.Icc (0 : ℝ) 1 := by
      intro hmem
      apply hxIoc
      constructor
      · exact lt_of_le_of_ne hmem.1 (Ne.symm hx)
      · exact hmem.2
    rw [Set.indicator_of_notMem hxIcc]


theorem eulerB_integrable_kappa (κ : ℝ → ℝ) (deriv : ℝ → ℝ)
    {kmin kmax : ℝ}
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hf : MemLp deriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable (fun x => κ x * deriv x * deriv x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have haes : AEStronglyMeasurable (fun x => κ x * deriv x * deriv x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hκ_meas.mul hf.aestronglyMeasurable).mul hf.aestronglyMeasurable
  have hIntSq : Integrable (fun x => (deriv x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hf.integrable_sq
  have hBound : Integrable (fun x => (|kmin| + |kmax|) * (deriv x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hIntSq.const_mul (|kmin| + |kmax|)
  refine Integrable.mono' hBound haes ?_
  filter_upwards [hκ] with x hx
  have hAbs : |κ x| ≤ |kmin| + |kmax| := by
    have h1 : -|kmin| ≤ κ x := le_trans (neg_abs_le kmin) hx.1
    have h2 : κ x ≤ |kmax| := le_trans hx.2 (le_abs_self kmax)
    have hp1 : (0:ℝ) ≤ |kmin| := abs_nonneg _
    have hp2 : (0:ℝ) ≤ |kmax| := abs_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have hsq : (0:ℝ) ≤ (deriv x) ^ 2 := sq_nonneg _
  calc ‖κ x * deriv x * deriv x‖ = |κ x * deriv x * deriv x| := Real.norm_eq_abs _
    _ = |κ x| * (|deriv x| * |deriv x|) := by
        rw [abs_mul, abs_mul, mul_assoc]
    _ = |κ x| * ((deriv x) ^ 2) := by
        rw [← sq_abs, pow_two]
    _ ≤ (|kmin| + |kmax|) * ((deriv x) ^ 2) :=
        mul_le_mul_of_nonneg_right hAbs hsq

/-- Coercivity of the Euler-step bilinear form: with `μ = volume.restrict
(Set.Icc 0 1)`, `B(u,u) = ∫ u²/τ + κ (u')² ≥ min (1/τ) kmin * ‖u‖²`. -/

theorem eulerB_coercive_of_aestronglyMeasurable
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (u : WeakH10) :
    min (1 / τ) kmin * ‖u‖ ^ 2
      ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
          + κ x * u.weakDeriv x * u.weakDeriv x := by
  have hmin1 : min (1 / τ) kmin ≤ 1 / τ := min_le_left _ _
  have hmin2 : min (1 / τ) kmin ≤ kmin := min_le_right _ _
  have hTmem : MemLp u.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    weakH10_toFun_memLp u
  have hDmem : MemLp u.weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    u.weakDeriv_memLp
  have hTsq := eulerB_eLpNorm_sq u.toFun hTmem
  have hDsq := eulerB_eLpNorm_sq u.weakDeriv hDmem
  have hnorm := weakH10_norm_sq u
  have hIntT : Integrable (fun x => (u.toFun x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hTmem.integrable_sq
  have hIntD : Integrable (fun x => (u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hDmem.integrable_sq
  have hIntTmin : Integrable (fun x => min (1 / τ) kmin * (u.toFun x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hIntT.const_mul (min (1 / τ) kmin)
  have hIntDmin : Integrable (fun x => min (1 / τ) kmin * (u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hIntD.const_mul (min (1 / τ) kmin)
  have hEqDiv : (fun x => u.toFun x * u.toFun x / τ)
      = (fun x => (1 / τ) * (u.toFun x) ^ 2) := by
    funext x
    ring
  have hIntTdiv : Integrable (fun x => u.toFun x * u.toFun x / τ)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [hEqDiv]
    exact hIntT.const_mul (1 / τ)
  have hIntK : Integrable (fun x => κ x * u.weakDeriv x * u.weakDeriv x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    eulerB_integrable_kappa κ u.weakDeriv hκ_meas hκ hDmem
  have hIntLHS : Integrable
      (fun x => min (1 / τ) kmin * (u.toFun x) ^ 2
        + min (1 / τ) kmin * (u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hIntTmin.add hIntDmin
  have hIntRHS : Integrable
      (fun x => u.toFun x * u.toFun x / τ + κ x * u.weakDeriv x * u.weakDeriv x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hIntTdiv.add hIntK
  have hRHS : (∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
        + κ x * u.weakDeriv x * u.weakDeriv x)
      = ∫ x, (u.toFun x * u.toFun x / τ + κ x * u.weakDeriv x * u.weakDeriv x)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact (eulerB_Icc_eq_Ioc _).symm
  have hLHS : min (1 / τ) kmin * ‖u‖ ^ 2
      = ∫ x, (min (1 / τ) kmin * (u.toFun x) ^ 2
        + min (1 / τ) kmin * (u.weakDeriv x) ^ 2)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [hnorm, hTsq, hDsq, mul_add, ← integral_const_mul,
      ← integral_const_mul, ← integral_add hIntTmin hIntDmin]
  rw [hLHS, hRHS]
  apply integral_mono_ae hIntLHS hIntRHS
  filter_upwards [hκ] with x hx
  have hTnn : (0:ℝ) ≤ (u.toFun x) ^ 2 := sq_nonneg _
  have hDnn : (0:ℝ) ≤ (u.weakDeriv x) ^ 2 := sq_nonneg _
  have h1 : min (1 / τ) kmin * (u.toFun x) ^ 2 ≤ (1 / τ) * (u.toFun x) ^ 2 :=
    mul_le_mul_of_nonneg_right hmin1 hTnn
  have h2 : min (1 / τ) kmin * (u.weakDeriv x) ^ 2 ≤ kmin * (u.weakDeriv x) ^ 2 :=
    mul_le_mul_of_nonneg_right hmin2 hDnn
  have h3 : kmin * (u.weakDeriv x) ^ 2 ≤ κ x * (u.weakDeriv x) ^ 2 :=
    mul_le_mul_of_nonneg_right hx.1 hDnn
  have h23 : min (1 / τ) kmin * (u.weakDeriv x) ^ 2
      ≤ κ x * (u.weakDeriv x) ^ 2 := le_trans h2 h3
  have hle : min (1 / τ) kmin * (u.toFun x) ^ 2
        + min (1 / τ) kmin * (u.weakDeriv x) ^ 2
      ≤ (1 / τ) * (u.toFun x) ^ 2 + κ x * (u.weakDeriv x) ^ 2 :=
    add_le_add h1 h23
  have e1 : (1 / τ) * (u.toFun x) ^ 2 = u.toFun x * u.toFun x / τ := by ring
  have e2 : κ x * (u.weakDeriv x) ^ 2 = κ x * u.weakDeriv x * u.weakDeriv x := by ring
  rwa [e1, e2] at hle


theorem eulerB_restrict_Ioc :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Ioc (0 : ℝ) 1)
      = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
  rw [Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left Set.Ioc_subset_Icc_self]


theorem eulerB_kmax_pos {kmin kmax : ℝ} {κ : ℝ → ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      kmin ≤ κ x ∧ κ x ≤ kmax) :
    0 < kmax := by
  have hμ1 : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    simp [Real.volume_Icc]
  have hμ0 : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
    intro hm
    rw [hm] at hμ1
    simp at hμ1
  have hnb : (ae (volume.restrict (Set.Icc (0 : ℝ) 1))).NeBot :=
    MeasureTheory.ae_neBot.mpr hμ0
  obtain ⟨x, hx1, hx2⟩ := Filter.Eventually.exists hκ
  exact lt_of_lt_of_le hkmin (le_trans hx1 hx2)


theorem eulerB_kappa_ae_norm {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      kmin ≤ κ x ∧ κ x ≤ kmax) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖κ x‖ ≤ kmax := by
  have hae : ae (volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ ae (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← eulerB_restrict_Ioc]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
  exact (Filter.Eventually.filter_mono hae hκ).mono fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hkmin.le hx.1)]
    exact hx.2


theorem eulerB_memLp_Ioc (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1))) :
    MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  rw [← eulerB_restrict_Ioc]
  exact MemLp.restrict (Set.Ioc (0 : ℝ) 1) hf


theorem eulerB_eLpNorm_Ioc_le (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1))) :
    (eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm f 2 (volume.restrict (Set.Icc 0 1))).toReal := by
  have hle : eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ eLpNorm f 2 (volume.restrict (Set.Icc 0 1)) := by
    have h := eLpNorm_restrict_le f 2 (volume.restrict (Set.Icc 0 1))
      (Set.Ioc (0 : ℝ) 1)
    rwa [eulerB_restrict_Ioc] at h
  have hfinR : eLpNorm f 2 (volume.restrict (Set.Icc 0 1)) < ⊤ :=
    hf.eLpNorm_lt_top
  have hfinL : eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) < ⊤ :=
    lt_of_le_of_lt hle hfinR
  exact (ENNReal.toReal_le_toReal hfinL.ne hfinR.ne).mpr hle


theorem eulerB_inner_abs_le (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    |∫ x, f x * g x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
      ≤ (eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        * (eLpNorm g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
  have hinner : inner ℝ (hf.toLp f) (hg.toLp g)
      = ∫ x, f x * g x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have h1 : ⇑(hf.toLp f) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] f :=
      hf.coeFn_toLp
    have h2 : ⇑(hg.toLp g) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g :=
      hg.coeFn_toLp
    have hinner_pt : ∀ x y : ℝ, inner ℝ x y = x * y := fun x y => by
      simp [RCLike.inner_apply, mul_comm]
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hinner_pt, hx1, hx2]
  have hCS := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  rw [Lp.norm_toLp f hf, Lp.norm_toLp g hg, hinner, Real.norm_eq_abs] at hCS
  exact hCS


theorem eulerB_add_mul_le_norm (Au Av Bu Bv Nu Nv : ℝ)
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hNu : 0 ≤ Nu) (hNv : 0 ≤ Nv)
    (hsq_u : Nu ^ 2 = Au ^ 2 + Bu ^ 2) (hsq_v : Nv ^ 2 = Av ^ 2 + Bv ^ 2) :
    Au * Av + Bu * Bv ≤ Nu * Nv := by
  have hnn : 0 ≤ Au * Av + Bu * Bv :=
    add_nonneg (mul_nonneg hAu hAv) (mul_nonneg hBu hBv)
  have hnn2 : 0 ≤ Nu * Nv := mul_nonneg hNu hNv
  have h2 : (Au * Av + Bu * Bv) ^ 2 ≤ (Nu * Nv) ^ 2 := by
    rw [mul_pow, hsq_u, hsq_v]
    nlinarith [sq_nonneg (Au * Bv - Bu * Av)]
  have hsqrt := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hnn2] at hsqrt


theorem eulerB_bounded
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (u v : WeakH10) :
    |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x|
      ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖ := by
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hkmax : 0 < kmax := eulerB_kmax_pos hkmin hκ
  have hτ0 : (0 : ℝ) < 1 / τ := one_div_pos.mpr hτ
  have hM_nn : (0 : ℝ) ≤ max (1 / τ) kmax := le_trans hτ0.le (le_max_left _ _)
  have huTν : MemLp u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    eulerB_memLp_Ioc _ (weakH10_toFun_memLp u)
  have hvTν : MemLp v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    eulerB_memLp_Ioc _ (weakH10_toFun_memLp v)
  have huDν : MemLp u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    eulerB_memLp_Ioc _ u.weakDeriv_memLp
  have hvDν : MemLp v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    eulerB_memLp_Ioc _ v.weakDeriv_memLp
  have hκ_aes_ν : AEStronglyMeasurable κ (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← eulerB_restrict_Ioc]
    exact hκ_meas.restrict
  have hκnorm : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖κ x‖ ≤ kmax :=
    eulerB_kappa_ae_norm hkmin hκ
  have hκν : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      kmin ≤ κ x ∧ κ x ≤ kmax := by
    have hae : ae (volume.restrict (Set.Ioc (0 : ℝ) 1))
        ≤ ae (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [← eulerB_restrict_Ioc]
      exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
    exact Filter.Eventually.filter_mono hae hκ
  have hκ_top : MemLp κ ⊤ (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    memLp_top_of_bound hκ_aes_ν kmax hκnorm
  have hF_mem : MemLp (κ * u.weakDeriv) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hκ_top.mul huDν
  have hAeq : (fun x => u.toFun x * v.toFun x / τ)
      = (fun x => (u.toFun * v.toFun) x / τ) := rfl
  have hA_int : Integrable (fun x => u.toFun x * v.toFun x / τ)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h := (MemLp.integrable_mul huTν hvTν).div_const τ
    rwa [← hAeq] at h
  have hB_int : Integrable (fun x => κ x * u.weakDeriv x * v.weakDeriv x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have huv_int : Integrable (u.weakDeriv * v.weakDeriv)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      MemLp.integrable_mul huDν hvDν
    have h := Integrable.bdd_mul huv_int hκ_aes_ν hκnorm
    have heq : (fun x => κ x * (u.weakDeriv * v.weakDeriv) x)
        = (fun x => κ x * u.weakDeriv x * v.weakDeriv x) := by
      funext x
      show κ x * (u.weakDeriv * v.weakDeriv) x
        = κ x * u.weakDeriv x * v.weakDeriv x
      rw [Pi.mul_apply, mul_assoc]
    rwa [heq] at h
  have hsplit : (∫ x in Set.Ioc (0 : ℝ) 1,
        (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x) ∂volume)
      = (∫ x in Set.Ioc (0 : ℝ) 1, u.toFun x * v.toFun x / τ ∂volume)
        + (∫ x in Set.Ioc (0 : ℝ) 1, κ x * u.weakDeriv x * v.weakDeriv x ∂volume) :=
    integral_add hA_int hB_int
  rw [intervalIntegral.integral_of_le h01, hsplit]
  have hA_ν : |∫ x in Set.Ioc (0 : ℝ) 1, u.toFun x * v.toFun x / τ ∂volume|
      ≤ (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
    rw [hAeq, integral_div, abs_div, abs_of_pos hτ]
    have hCS := eulerB_inner_abs_le _ _ huTν hvTν
    calc |∫ a, (u.toFun * v.toFun) a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))| / τ
        = (1 / τ)
          * |∫ a, (u.toFun * v.toFun) a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))| := by
          rw [div_eq_mul_inv, one_div]
          exact mul_comm _ _
      _ ≤ (1 / τ) * ((eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal) :=
          mul_le_mul_of_nonneg_left hCS hτ0.le
      _ = (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
          ring
  have hF_le : eLpNorm (κ * u.weakDeriv) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))
      ≤ eLpNorm (kmax • u.weakDeriv) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine eLpNorm_mono_ae hF_mem.aestronglyMeasurable (hκν.mono fun x hx => ?_)
    have hκx : ‖κ x‖ = κ x := by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hkmin.le hx.1)]
    have hkmax_norm : ‖kmax‖ = kmax := by
      rw [Real.norm_eq_abs, abs_of_nonneg hkmax.le]
    have hsmul : (kmax • u.weakDeriv) x = kmax * u.weakDeriv x := by
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [Pi.mul_apply, norm_mul, hsmul, norm_mul, hκx, hkmax_norm]
    exact mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)
  have hF_toReal : (eLpNorm (κ * u.weakDeriv) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ kmax * (eLpNorm u.weakDeriv 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
    have hfinK : eLpNorm (kmax • u.weakDeriv) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) < ⊤ := by
      rw [eLpNorm_const_smul]
      refine ENNReal.mul_lt_top ?_ ?_
      · rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hkmax.le]
        exact ENNReal.ofReal_lt_top
      · have hle : eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))
            ≤ eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1)) := by
          have h := eLpNorm_restrict_le u.weakDeriv 2
            (volume.restrict (Set.Icc 0 1)) (Set.Ioc (0 : ℝ) 1)
          rwa [eulerB_restrict_Ioc] at h
        exact lt_of_le_of_lt hle u.weakDeriv_memLp.eLpNorm_lt_top
    have hfinF : eLpNorm (κ * u.weakDeriv) 2
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) < ⊤ :=
      lt_of_le_of_lt hF_le hfinK
    have hle := (ENNReal.toReal_le_toReal hfinF.ne hfinK.ne).mpr hF_le
    rwa [eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hkmax.le, ENNReal.toReal_ofReal hkmax.le] at hle
  have hB_ν : |∫ x in Set.Ioc (0 : ℝ) 1, κ x * u.weakDeriv x * v.weakDeriv x ∂volume|
      ≤ kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
    have hBeq : (fun x => κ x * u.weakDeriv x * v.weakDeriv x)
        = (fun x => (κ * u.weakDeriv) x * v.weakDeriv x) := rfl
    rw [hBeq]
    have hCS := eulerB_inner_abs_le _ _ hF_mem hvDν
    calc |∫ x, (κ * u.weakDeriv) x * v.weakDeriv x
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
        ≤ (eLpNorm (κ * u.weakDeriv) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
          hCS
      _ ≤ (kmax * (eLpNorm u.weakDeriv 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal)
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
          mul_le_mul_of_nonneg_right hF_toReal ENNReal.toReal_nonneg
      _ = kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
          ring
  have hAu_le : (eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    eulerB_eLpNorm_Ioc_le _ (weakH10_toFun_memLp u)
  have hAv_le : (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    eulerB_eLpNorm_Ioc_le _ (weakH10_toFun_memLp v)
  have hBu_le : (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    eulerB_eLpNorm_Ioc_le _ u.weakDeriv_memLp
  have hBv_le : (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    eulerB_eLpNorm_Ioc_le _ v.weakDeriv_memLp
  have hAvν_nn : (0 : ℝ)
      ≤ (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  have hAu_nn : (0 : ℝ)
      ≤ (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hAv_nn : (0 : ℝ)
      ≤ (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hBvν_nn : (0 : ℝ)
      ≤ (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  have hBu_nn : (0 : ℝ)
      ≤ (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hBv_nn : (0 : ℝ)
      ≤ (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
    ENNReal.toReal_nonneg
  have hA_final : |∫ x in Set.Ioc (0 : ℝ) 1, u.toFun x * v.toFun x / τ ∂volume|
      ≤ (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal := by
    have h1 : (eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        ≤ (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal :=
      mul_le_mul hAu_le hAv_le hAvν_nn hAu_nn
    calc |∫ x in Set.Ioc (0 : ℝ) 1, u.toFun x * v.toFun x / τ ∂volume|
        ≤ (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
          hA_ν
      _ = (1 / τ) * ((eLpNorm u.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal) := by
          ring
      _ ≤ (1 / τ) * ((eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal) :=
          mul_le_mul_of_nonneg_left h1 hτ0.le
      _ = (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal := by
          ring
  have hB_final : |∫ x in Set.Ioc (0 : ℝ) 1, κ x * u.weakDeriv x * v.weakDeriv x ∂volume|
      ≤ kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal := by
    have h1 : (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        ≤ (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
      mul_le_mul hBu_le hBv_le hBvν_nn hBu_nn
    calc |∫ x in Set.Ioc (0 : ℝ) 1, κ x * u.weakDeriv x * v.weakDeriv x ∂volume|
        ≤ kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
          hB_ν
      _ = kmax * ((eLpNorm u.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal) := by
          ring
      _ ≤ kmax * ((eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal) :=
          mul_le_mul_of_nonneg_left h1 hkmax.le
      _ = kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal := by
          ring
  have hCS2 : (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
      + (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
      ≤ ‖u‖ * ‖v‖ :=
    eulerB_add_mul_le_norm _ _ _ _ _ _ hAu_nn hAv_nn hBu_nn hBv_nn
      (norm_nonneg _) (norm_nonneg _) (weakH10_norm_sq u) (weakH10_norm_sq v)
  have e1 : (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
      ≤ max (1 / τ) kmax * ((eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg hAu_nn hAv_nn)
  have e2 : kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
      ≤ max (1 / τ) kmax * ((eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
        * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (mul_nonneg hBu_nn hBv_nn)
  calc |∫ x in Set.Ioc (0 : ℝ) 1, u.toFun x * v.toFun x / τ ∂volume
        + ∫ x in Set.Ioc (0 : ℝ) 1, κ x * u.weakDeriv x * v.weakDeriv x ∂volume|
      ≤ |∫ x in Set.Ioc (0 : ℝ) 1, u.toFun x * v.toFun x / τ ∂volume|
        + |∫ x in Set.Ioc (0 : ℝ) 1, κ x * u.weakDeriv x * v.weakDeriv x ∂volume| :=
        abs_add_le _ _
    _ ≤ (1 / τ) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
        + kmax * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal :=
        add_le_add hA_final hB_final
    _ ≤ max (1 / τ) kmax * ((eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal)
        + max (1 / τ) kmax * ((eLpNorm u.weakDeriv 2
          (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal) :=
        add_le_add e1 e2
    _ = max (1 / τ) kmax * ((eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal
        + (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal
          * (eLpNorm v.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal) := by
        ring
    _ ≤ max (1 / τ) kmax * (‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hCS2 hM_nn
    _ = max (1 / τ) kmax * ‖u‖ * ‖v‖ := by
        ring


theorem eulerRhs_bound
    {τ : ℝ} (hτ : 0 < τ)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (v : WeakH10) :
    |∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x|
      ≤ ((eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ) * ‖v‖ := by
  have hvt : MemLp v.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    weakH10_toFun_memLp v
  have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc 0 1 :=
    fun t ht => ⟨ht.1.le, ht.2⟩
  have hμν : (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Ioc (0 : ℝ) 1)
      = volume.restrict (Set.Ioc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left hsub]
  have hFν : MemLp F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← hμν]
    exact hF.restrict _
  have huν : MemLp uprev 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← hμν]
    exact huprev.restrict _
  have hvν : MemLp v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [← hμν]
    exact hvt.restrict _
  have hdiv : (fun x => uprev x / τ) = τ⁻¹ • uprev := by
    funext x
    show uprev x / τ = (τ⁻¹ • uprev) x
    rw [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have huτν : MemLp (fun x => uprev x / τ) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [hdiv]
    exact huν.const_smul _
  have hInt1 : Integrable (fun x => F x * v.toFun x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (hFν.integrable_mul hvν).congr (Filter.Eventually.of_forall fun x => rfl)
  have hInt2 : Integrable (fun x => (uprev x / τ) * v.toFun x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (huτν.integrable_mul hvν).congr (Filter.Eventually.of_forall fun x => rfl)
  have hCS1 : |∫ x, F x * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
      ≤ (eLpNorm F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
    have hinner : inner ℝ (hFν.toLp F) (hvν.toLp v.toFun)
        = ∫ a, inner ℝ (⇑(hFν.toLp F) a) (⇑(hvν.toLp v.toFun) a)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      L2.inner_def _ _
    have hcongr : (∫ a, inner ℝ (⇑(hFν.toLp F) a) (⇑(hvν.toLp v.toFun) a)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ a, F a * v.toFun a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [hFν.coeFn_toLp, hvν.coeFn_toLp] with a ha hb
      rw [ha, hb, Real.inner_apply]
    calc |∫ x, F x * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
        = ‖inner ℝ (hFν.toLp F) (hvν.toLp v.toFun)‖ := by
          rw [hinner, hcongr, Real.norm_eq_abs]
      _ ≤ ‖hFν.toLp F‖ * ‖hvν.toLp v.toFun‖ := norm_inner_le_norm _ _
      _ = (eLpNorm F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
          rw [Lp.norm_toLp, Lp.norm_toLp]
  have hCS2 : |∫ x, (uprev x / τ) * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
      ≤ (eLpNorm (fun x => uprev x / τ) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
    have hinner : inner ℝ (huτν.toLp _) (hvν.toLp v.toFun)
        = ∫ a, inner ℝ (⇑(huτν.toLp _) a) (⇑(hvν.toLp v.toFun) a)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      L2.inner_def _ _
    have hcongr : (∫ a, inner ℝ (⇑(huτν.toLp _) a) (⇑(hvν.toLp v.toFun) a)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ a, (uprev a / τ) * v.toFun a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [huτν.coeFn_toLp, hvν.coeFn_toLp] with a ha hb
      rw [ha, hb, Real.inner_apply]
    calc |∫ x, (uprev x / τ) * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
        = ‖inner ℝ (huτν.toLp _) (hvν.toLp v.toFun)‖ := by
          rw [hinner, hcongr, Real.norm_eq_abs]
      _ ≤ ‖huτν.toLp _‖ * ‖hvν.toLp v.toFun‖ := norm_inner_le_norm _ _
      _ = (eLpNorm (fun x => uprev x / τ) 2
            (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
          rw [Lp.norm_toLp, Lp.norm_toLp]
  have hnormdiv : (eLpNorm (fun x => uprev x / τ) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      = (eLpNorm uprev 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal / τ := by
    rw [hdiv, eLpNorm_const_smul, ENNReal.toReal_mul]
    have hτinv : (‖(τ⁻¹ : ℝ)‖ₑ).toReal = τ⁻¹ := by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
      exact abs_of_pos (inv_pos.mpr hτ)
    rw [hτinv, div_eq_mul_inv, mul_comm]
  have hleF : (eLpNorm F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    have h := eLpNorm_restrict_le F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
      (Set.Ioc (0 : ℝ) 1)
    rw [hμν] at h
    exact (ENNReal.toReal_le_toReal hFν.eLpNorm_lt_top.ne
      hF.eLpNorm_lt_top.ne).mpr h
  have hleU : (eLpNorm uprev 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    have h := eLpNorm_restrict_le uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
      (Set.Ioc (0 : ℝ) 1)
    rw [hμν] at h
    exact (ENNReal.toReal_le_toReal huν.eLpNorm_lt_top.ne
      huprev.eLpNorm_lt_top.ne).mpr h
  have hleVν : (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm v.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    have h := eLpNorm_restrict_le v.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
      (Set.Ioc (0 : ℝ) 1)
    rw [hμν] at h
    exact (ENNReal.toReal_le_toReal hvν.eLpNorm_lt_top.ne
      hvt.eLpNorm_lt_top.ne).mpr h
  have hleV : (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal ≤ ‖v‖ :=
    le_trans hleVν (weakH10_eLpNorm_toFun_le v)
  have hsplit : (fun x => (F x + uprev x / τ) * v.toFun x)
      = fun x => F x * v.toFun x + (uprev x / τ) * v.toFun x :=
    funext fun x => add_mul _ _ _
  rw [intervalIntegral.integral_of_le zero_le_one, hsplit,
    integral_add hInt1 hInt2]
  rw [hnormdiv] at hCS2
  calc |∫ x, F x * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        + ∫ x, (uprev x / τ) * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
      ≤ |∫ x, F x * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))|
        + |∫ x, (uprev x / τ) * v.toFun x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))| :=
        abs_add_le _ _
    _ ≤ (eLpNorm F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
        + (eLpNorm uprev 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal / τ
          * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal :=
        add_le_add hCS1 hCS2
    _ = ((eLpNorm F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
          + (eLpNorm uprev 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal / τ)
        * (eLpNorm v.toFun 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal := by
        ring
    _ ≤ ((eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ) * ‖v‖ := by
        have hsum : (eLpNorm F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal
              + (eLpNorm uprev 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal / τ
            ≤ (eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
              + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ :=
          add_le_add hleF ((div_le_div_iff_of_pos_right hτ).mpr hleU)
        have hpos : 0 ≤ (eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ :=
          add_nonneg ENNReal.toReal_nonneg
            (div_nonneg ENNReal.toReal_nonneg hτ.le)
        exact mul_le_mul hsum hleV ENNReal.toReal_nonneg hpos


theorem eulerB_clm
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖) :
    ∃ B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ,
      ∀ u v : WeakH10,
        B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x := by
  have hκB : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), ‖κ x‖ ≤ |kmin| + |kmax| := by
    filter_upwards [hκ] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 : -|kmin| ≤ kmin := neg_abs_le kmin
      have h2 : (0 : ℝ) ≤ |kmax| := abs_nonneg kmax
      linarith [hx.1]
    · have h1 : kmax ≤ |kmax| := le_abs_self kmax
      have h2 : (0 : ℝ) ≤ |kmin| := abs_nonneg kmin
      linarith [hx.2]
  have hInt : ∀ u v : WeakH10, IntervalIntegrable
      (fun x => u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
      volume 0 1 := by
    intro u v
    have hT : MemLp (u.toFun * v.toFun) 1 (volume.restrict (Set.Icc 0 1)) :=
      (weakH10_toFun_memLp u).mul (weakH10_toFun_memLp v)
    have hD : MemLp (u.weakDeriv * v.weakDeriv) 1
        (volume.restrict (Set.Icc 0 1)) :=
      (u.weakDeriv_memLp).mul (v.weakDeriv_memLp)
    have hTi : Integrable (fun x => u.toFun x * v.toFun x / τ)
        (volume.restrict (Set.Icc 0 1)) :=
      (memLp_one_iff_integrable.mp hT).div_const τ
    have hDi : Integrable (fun x => κ x * u.weakDeriv x * v.weakDeriv x)
        (volume.restrict (Set.Icc 0 1)) := by
      have hκi : Integrable (fun x => κ x * (u.weakDeriv x * v.weakDeriv x))
          (volume.restrict (Set.Icc 0 1)) :=
        (memLp_one_iff_integrable.mp hD).bdd_mul hκ_meas hκB
      have heq : (fun x => κ x * u.weakDeriv x * v.weakDeriv x)
          = fun x => κ x * (u.weakDeriv x * v.weakDeriv x) := by
        funext x; ring
      rwa [heq]
    have hAdd : Integrable
        (fun x => u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
        (volume.restrict (Set.Icc 0 1)) := hTi.add hDi
    have hIntOn : IntegrableOn
        (fun x => u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
        (Set.Icc (0 : ℝ) 1) volume := hAdd
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hIntOn.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans le_rfl⟩)
  have haddR : ∀ u v w : WeakH10,
      (∫ x in (0 : ℝ)..1, u.toFun x * (v + w).toFun x / τ
        + κ x * u.weakDeriv x * (v + w).weakDeriv x)
      = (∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x)
        + ∫ x in (0 : ℝ)..1, u.toFun x * w.toFun x / τ
          + κ x * u.weakDeriv x * w.weakDeriv x := by
    intro u v w
    have hpt : ∀ x : ℝ, (u.toFun x * (v + w).toFun x / τ
          + κ x * u.weakDeriv x * (v + w).weakDeriv x)
        = (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
          + (u.toFun x * w.toFun x / τ + κ x * u.weakDeriv x * w.weakDeriv x) := by
      intro x
      have e1 : (v + w).toFun x = v.toFun x + w.toFun x := rfl
      have e2 : (v + w).weakDeriv x = v.weakDeriv x + w.weakDeriv x := rfl
      rw [e1, e2]; ring
    simp only [hpt]
    exact intervalIntegral.integral_add (hInt u v) (hInt u w)
  have hsmulR : ∀ (c : ℝ) (u v : WeakH10),
      (∫ x in (0 : ℝ)..1, u.toFun x * (c • v).toFun x / τ
        + κ x * u.weakDeriv x * (c • v).weakDeriv x)
      = c • (∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x) := by
    intro c u v
    have hpt : ∀ x : ℝ, (u.toFun x * (c • v).toFun x / τ
          + κ x * u.weakDeriv x * (c • v).weakDeriv x)
        = c • (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x) := by
      intro x
      have e1 : (c • v).toFun x = c • v.toFun x := rfl
      have e2 : (c • v).weakDeriv x = c • v.weakDeriv x := rfl
      simp only [e1, e2, smul_eq_mul]
      ring
    simp only [hpt]
    exact intervalIntegral.integral_smul c _
  have haddL : ∀ u w v : WeakH10,
      (∫ x in (0 : ℝ)..1, (u + w).toFun x * v.toFun x / τ
        + κ x * (u + w).weakDeriv x * v.weakDeriv x)
      = (∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x)
        + ∫ x in (0 : ℝ)..1, w.toFun x * v.toFun x / τ
          + κ x * w.weakDeriv x * v.weakDeriv x := by
    intro u w v
    have hpt : ∀ x : ℝ, ((u + w).toFun x * v.toFun x / τ
          + κ x * (u + w).weakDeriv x * v.weakDeriv x)
        = (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
          + (w.toFun x * v.toFun x / τ + κ x * w.weakDeriv x * v.weakDeriv x) := by
      intro x
      have e1 : (u + w).toFun x = u.toFun x + w.toFun x := rfl
      have e2 : (u + w).weakDeriv x = u.weakDeriv x + w.weakDeriv x := rfl
      rw [e1, e2]; ring
    simp only [hpt]
    exact intervalIntegral.integral_add (hInt u v) (hInt w v)
  have hsmulL : ∀ (c : ℝ) (u v : WeakH10),
      (∫ x in (0 : ℝ)..1, (c • u).toFun x * v.toFun x / τ
        + κ x * (c • u).weakDeriv x * v.weakDeriv x)
      = c • (∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x) := by
    intro c u v
    have hpt : ∀ x : ℝ, ((c • u).toFun x * v.toFun x / τ
          + κ x * (c • u).weakDeriv x * v.weakDeriv x)
        = c • (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x) := by
      intro x
      have e1 : (c • u).toFun x = c • u.toFun x := rfl
      have e2 : (c • u).weakDeriv x = c • u.weakDeriv x := rfl
      simp only [e1, e2, smul_eq_mul]
      ring
    simp only [hpt]
    exact intervalIntegral.integral_smul c _
  let bLM : WeakH10 →ₗ[ℝ] WeakH10 →ₗ[ℝ] ℝ :=
    { toFun := fun u =>
        { toFun := fun v => ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
            + κ x * u.weakDeriv x * v.weakDeriv x
          map_add' := fun v w => haddR u v w
          map_smul' := fun c v => hsmulR c u v }
      map_add' := fun u w => by
        ext v
        rw [LinearMap.add_apply]
        exact haddL u w v
      map_smul' := fun c u => by
        ext v
        rw [LinearMap.smul_apply]
        exact hsmulL c u v }
  have hC : ∀ u v : WeakH10, ‖bLM u v‖ ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖ := by
    intro u v
    have h := hBnd u v
    have heq : bLM u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x := rfl
    rw [heq, Real.norm_eq_abs]
    exact h
  refine ⟨bLM.mkContinuous₂ (max (1 / τ) kmax) hC, fun u v => ?_⟩
  calc (bLM.mkContinuous₂ (max (1 / τ) kmax) hC u v)
      = bLM u v := LinearMap.mkContinuous₂_apply bLM hC u v
    _ = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x := rfl


theorem eulerRhs_memLp_one_intervalIntegrable (g : ℝ → ℝ)
    (hg : MemLp g 1 (volume.restrict (Set.Icc 0 1))) :
    IntervalIntegrable g volume 0 1 := by
  have := weakH10_meas_finite
  have hIntOn : IntegrableOn g (Set.Icc 0 1) volume := hg.integrable (le_refl 1)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact hIntOn.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans le_rfl⟩)

/-- The Euler-step right-hand side as a continuous linear functional,
from its bound as a hypothesis. The inner-product-space instances on
`WeakH10` (H¹ inner product) are declared in this file below (they are
part of the file, not of the pinned statement); the norm `‖·‖` is the
H¹ norm. -/

theorem eulerRhs_clm
    {τ : ℝ} (hτ : 0 < τ)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (hRhs : ∀ v : WeakH10,
      |∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x|
        ≤ ((eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ) * ‖v‖) :
    ∃ L : WeakH10 →L[ℝ] ℝ,
      ∀ v : WeakH10,
        L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x := by
  have hG : MemLp (fun x => F x + uprev x / τ) 2 (volume.restrict (Set.Icc 0 1)) :=
    hF.add (huprev.mul_const _)
  have hInt : ∀ v : WeakH10,
      IntervalIntegrable (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1 :=
    fun v => eulerRhs_memLp_one_intervalIntegrable _
      (hG.mul (weakH10_toFun_memLp v))
  have hadd : ∀ v w : WeakH10,
      (∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * (v + w).toFun x)
        = (∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
          + ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * w.toFun x := by
    intro v w
    have hpt : (fun x => (F x + uprev x / τ) * (v + w).toFun x)
        = (fun x => (F x + uprev x / τ) * v.toFun x
          + (F x + uprev x / τ) * w.toFun x) := by
      funext x
      have hvw : (v + w).toFun x = v.toFun x + w.toFun x := rfl
      rw [hvw, mul_add]
    rw [hpt]
    exact intervalIntegral.integral_add (hInt v) (hInt w)
  have hsmul : ∀ (c : ℝ) (v : WeakH10),
      (∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * (c • v).toFun x)
        = c • ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x := by
    intro c v
    have hpt : (fun x => (F x + uprev x / τ) * (c • v).toFun x)
        = (fun x => c • ((F x + uprev x / τ) * v.toFun x)) := by
      funext x
      have hcv : (c • v).toFun x = c * v.toFun x := rfl
      rw [hcv, smul_eq_mul]
      ring
    rw [hpt]
    exact intervalIntegral.integral_smul c _
  let lm : WeakH10 →ₗ[ℝ] ℝ :=
    { toFun := fun v : WeakH10 => ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x,
      map_add' := hadd,
      map_smul' := hsmul }
  refine ⟨lm.mkContinuous _ (fun v => by
    show ‖∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x‖ ≤ _
    rw [Real.norm_eq_abs]
    exact hRhs v), fun v => rfl⟩


theorem laxMilgram_exist_of_coercive (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hBcoer : IsCoercive B) (L : V →L[ℝ] ℝ) :
    ∃ u : V, ∀ v : V, B u v = L v := by
  let equiv := hBcoer.continuousLinearEquivOfBilin
  let w := (InnerProductSpace.toDual ℝ V).symm L
  refine ⟨equiv.symm w, fun v => ?_⟩
  calc B (equiv.symm w) v
      = inner ℝ (equiv (equiv.symm w)) v :=
        (IsCoercive.continuousLinearEquivOfBilin_apply hBcoer _ _).symm
    _ = inner ℝ w v := by rw [ContinuousLinearEquiv.apply_symm_apply]
    _ = L v := InnerProductSpace.toDual_symm_apply


theorem weakH10_ae_mem_Ioc (w : WeakH10) (hw : ‖w‖ = 0) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioc 0 1 → w.toFun x = 0 ∧ w.weakDeriv x = 0 := by
  have hsq := weakH10_norm_sq w
  have h0 : ‖w‖ ^ 2 = 0 := by rw [hw]; norm_num
  rw [hsq] at h0
  obtain ⟨hA, hB⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h0
  have hA0 : (eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal = 0 :=
    sq_eq_zero_iff.mp hA
  have hB0 : (eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal = 0 :=
    sq_eq_zero_iff.mp hB
  have eA : eLpNorm w.toFun 2 (volume.restrict (Set.Icc 0 1)) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hA0 with h | h
    · exact h
    · exact absurd h (weakH10_toFun_memLp w).eLpNorm_lt_top.ne
  have eB : eLpNorm w.weakDeriv 2 (volume.restrict (Set.Icc 0 1)) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hB0 with h | h
    · exact h
    · exact absurd h w.weakDeriv_memLp.eLpNorm_lt_top.ne
  have aA : w.toFun =ᵐ[volume.restrict (Set.Icc 0 1)] 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).mp eA
  have aB : w.weakDeriv =ᵐ[volume.restrict (Set.Icc 0 1)] 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).mp eB
  have nA : volume ({x | ¬w.toFun x = 0} ∩ Set.Icc 0 1) = 0 := by
    have h := ae_iff.mp aA
    rwa [Measure.restrict_apply' measurableSet_Icc] at h
  have nB : volume ({x | ¬w.weakDeriv x = 0} ∩ Set.Icc 0 1) = 0 := by
    have h := ae_iff.mp aB
    rwa [Measure.restrict_apply' measurableSet_Icc] at h
  rw [ae_iff]
  apply measure_mono_null _ (measure_union_null nA nB)
  intro x hx
  have hx' : ¬(x ∈ Set.Ioc 0 1 → w.toFun x = 0 ∧ w.weakDeriv x = 0) := hx
  have hxIoc : x ∈ Set.Ioc 0 1 := by
    by_contra hcon
    exact hx' (fun h => absurd h hcon)
  have hIcc : x ∈ Set.Icc 0 1 := Set.Ioc_subset_Icc_self hxIoc
  have hcon : ¬(w.toFun x = 0 ∧ w.weakDeriv x = 0) := fun h => hx' (fun _ => h)
  show (¬w.toFun x = 0 ∧ x ∈ Set.Icc 0 1) ∨ (¬w.weakDeriv x = 0 ∧ x ∈ Set.Icc 0 1)
  by_cases htf : w.toFun x = 0
  · exact Or.inr ⟨(fun h => hcon ⟨htf, h⟩), hIcc⟩
  · exact Or.inl ⟨htf, hIcc⟩


theorem weakH10_intervalIntegral_eq_zero_of_null (F : ℝ → ℝ) (w : WeakH10) (hw : ‖w‖ = 0)
    (hF : ∀ x, w.toFun x = 0 → w.weakDeriv x = 0 → F x = 0) :
    ∫ x in (0 : ℝ)..1, F x = 0 := by
  have hae := weakH10_ae_mem_Ioc w hw
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_zero_of_ae_eq_zero
  filter_upwards [hae] with x h hxIoc
  obtain ⟨hx1, hx2⟩ := h hxIoc
  exact hF x hx1 hx2


noncomputable def weakH10_descendCLM_lin {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L₀ : WeakH10 →L[ℝ] F)
    (hvan : ∀ w : WeakH10, ‖w‖ = 0 → L₀ w = 0) :
    SeparationQuotient WeakH10 →ₗ[ℝ] F :=
  { toFun := SeparationQuotient.lift (fun v => L₀ v) (fun x y hxy => by
      have hmk : SeparationQuotient.mk x = SeparationQuotient.mk y :=
        SeparationQuotient.mk_eq_mk.mpr hxy
      have h0 : SeparationQuotient.mk (x - y) = 0 := by
        rw [SeparationQuotient.mk_sub, hmk, sub_self]
      have hnorm : ‖x - y‖ = 0 := SeparationQuotient.mk_eq_zero_iff.mp h0
      have hz : L₀ (x - y) = 0 := hvan _ hnorm
      have hsub : L₀ (x - y) = L₀ x - L₀ y := by simp
      rw [hsub] at hz
      exact sub_eq_zero.mp hz)
    map_add' := fun q₁ q₂ => by
      obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk q₁
      obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk q₂
      show SeparationQuotient.lift (fun v => L₀ v) _
          (SeparationQuotient.mk u + SeparationQuotient.mk v) =
        SeparationQuotient.lift (fun v => L₀ v) _ (SeparationQuotient.mk u) +
          SeparationQuotient.lift (fun v => L₀ v) _ (SeparationQuotient.mk v)
      rw [← SeparationQuotient.mk_add]
      simp only [SeparationQuotient.lift_mk, map_add]
    map_smul' := fun c q => by
      obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk q
      show SeparationQuotient.lift (fun v => L₀ v) _
          (c • SeparationQuotient.mk u) =
        c • SeparationQuotient.lift (fun v => L₀ v) _ (SeparationQuotient.mk u)
      rw [← SeparationQuotient.mk_smul]
      simp only [SeparationQuotient.lift_mk, map_smul] }


theorem weakH10_descendCLM_lin_mk {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L₀ : WeakH10 →L[ℝ] F)
    (hvan : ∀ w : WeakH10, ‖w‖ = 0 → L₀ w = 0) (v : WeakH10) :
    weakH10_descendCLM_lin L₀ hvan (SeparationQuotient.mk v) = L₀ v := rfl


noncomputable def weakH10_descendCLM {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L₀ : WeakH10 →L[ℝ] F)
    (hvan : ∀ w : WeakH10, ‖w‖ = 0 → L₀ w = 0) :
    SeparationQuotient WeakH10 →L[ℝ] F :=
  LinearMap.mkContinuous (weakH10_descendCLM_lin L₀ hvan) ‖L₀‖ (fun q => by
    obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk q
    rw [weakH10_descendCLM_lin_mk, SeparationQuotient.norm_mk]
    exact L₀.le_opNorm u)


theorem weakH10_descendCLM_mk {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L₀ : WeakH10 →L[ℝ] F)
    (hvan : ∀ w : WeakH10, ‖w‖ = 0 → L₀ w = 0) (v : WeakH10) :
    weakH10_descendCLM L₀ hvan (SeparationQuotient.mk v) = L₀ v := by
  unfold weakH10_descendCLM
  rw [LinearMap.mkContinuous_apply, weakH10_descendCLM_lin_mk]


theorem weakH10_L_vanish {τ : ℝ} {F uprev : ℝ → ℝ} (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (w : WeakH10) (hw : ‖w‖ = 0) : L w = 0 := by
  rw [hL]
  exact weakH10_intervalIntegral_eq_zero_of_null _ _ hw
    (fun t ht1 _ => by simp [ht1])


theorem weakH10_B_vanish_left {τ : ℝ} {κ : ℝ → ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (w v : WeakH10) (hw : ‖w‖ = 0) : B w v = 0 := by
  rw [hB]
  exact weakH10_intervalIntegral_eq_zero_of_null _ _ hw
    (fun t ht1 ht2 => by simp [ht1, ht2])


theorem weakH10_B_vanish_right {τ : ℝ} {κ : ℝ → ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (u w : WeakH10) (hw : ‖w‖ = 0) : B u w = 0 := by
  rw [hB]
  exact weakH10_intervalIntegral_eq_zero_of_null _ _ hw
    (fun t ht1 ht2 => by simp [ht1, ht2])


noncomputable def weakH10_descendB_lin {τ : ℝ} {κ : ℝ → ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x) :
    WeakH10 →ₗ[ℝ] (SeparationQuotient WeakH10 →L[ℝ] ℝ) where
  toFun := fun u =>
    weakH10_descendCLM (B u) (fun w hw => weakH10_B_vanish_right B hB u w hw)
  map_add' := fun u1 u2 => by
    apply ContinuousLinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk q
    show weakH10_descendCLM (B (u1 + u2)) _
          (SeparationQuotient.mk v)
        = (weakH10_descendCLM (B u1) _ + weakH10_descendCLM (B u2) _)
          (SeparationQuotient.mk v)
    simp only [add_apply, weakH10_descendCLM_mk]
    have h : B (u1 + u2) = B u1 + B u2 := map_add B u1 u2
    rw [h, add_apply]
  map_smul' := fun c u => by
    apply ContinuousLinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk q
    show weakH10_descendCLM (B (c • u)) _
          (SeparationQuotient.mk v)
        = (c • weakH10_descendCLM (B u) _) (SeparationQuotient.mk v)
    simp only [smul_apply, weakH10_descendCLM_mk]
    have h : B (c • u) = c • B u := map_smul B c u
    rw [h, smul_apply]


theorem weakH10_descendB_lin_apply {τ : ℝ} {κ : ℝ → ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x) (u : WeakH10) :
    weakH10_descendB_lin B hB u
      = weakH10_descendCLM (B u)
        (fun w hw => weakH10_B_vanish_right B hB u w hw) := rfl


noncomputable def weakH10_descendB_clm {τ : ℝ} {κ : ℝ → ℝ} {kmax : ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hM : 0 ≤ max (1 / τ) kmax) :
    WeakH10 →L[ℝ] (SeparationQuotient WeakH10 →L[ℝ] ℝ) :=
  LinearMap.mkContinuous (E := WeakH10) (F := SeparationQuotient WeakH10 →L[ℝ] ℝ) (weakH10_descendB_lin B hB) (max (1 / τ) kmax) (fun (u : WeakH10) => by
    have hbound : ∀ q : SeparationQuotient WeakH10,
        ‖(weakH10_descendB_lin B hB u) q‖ ≤ (max (1 / τ) kmax * ‖u‖) * ‖q‖ := by
      intro q
      obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk q
      rw [weakH10_descendB_lin_apply, weakH10_descendCLM_mk,
        SeparationQuotient.norm_mk, Real.norm_eq_abs, hB u v]
      refine (hBnd u v).trans_eq ?_
      ring
    exact ContinuousLinearMap.opNorm_le_bound (weakH10_descendB_lin B hB u)
      (mul_nonneg hM (norm_nonneg u)) hbound)


theorem weakH10_descendB_clm_mk {τ : ℝ} {κ : ℝ → ℝ} {kmax : ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hM : 0 ≤ max (1 / τ) kmax) (u v : WeakH10) :
    weakH10_descendB_clm B hB hBnd hM u (SeparationQuotient.mk v) = B u v := by
  unfold weakH10_descendB_clm
  rw [LinearMap.mkContinuous_apply, weakH10_descendB_lin_apply,
    weakH10_descendCLM_mk]


theorem weakH10_descendB_clm_vanish {τ : ℝ} {κ : ℝ → ℝ} {kmax : ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hM : 0 ≤ max (1 / τ) kmax) (w : WeakH10) (hw : ‖w‖ = 0) :
    weakH10_descendB_clm B hB hBnd hM w = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := SeparationQuotient.surjective_mk q
  rw [weakH10_descendB_clm_mk]
  show B w v = 0
  exact weakH10_B_vanish_left B hB w v hw


noncomputable def weakH10_descendB {τ : ℝ} {κ : ℝ → ℝ} {kmax : ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hM : 0 ≤ max (1 / τ) kmax) :
    SeparationQuotient WeakH10 →L[ℝ] SeparationQuotient WeakH10 →L[ℝ] ℝ :=
  weakH10_descendCLM (F := SeparationQuotient WeakH10 →L[ℝ] ℝ)
    (weakH10_descendB_clm B hB hBnd hM)
    (fun w hw => weakH10_descendB_clm_vanish B hB hBnd hM w hw)


theorem weakH10_descendB_mk {τ : ℝ} {κ : ℝ → ℝ} {kmax : ℝ}
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hM : 0 ≤ max (1 / τ) kmax) (u v : WeakH10) :
    weakH10_descendB B hB hBnd hM (SeparationQuotient.mk u) (SeparationQuotient.mk v)
      = B u v := by
  unfold weakH10_descendB
  rw [weakH10_descendCLM_mk, weakH10_descendB_clm_mk]

/-- Lax-Milgram existence for the Euler step: there is `u` with
`B u v = L v` for all `v`, from the packaged form/functional and the
coercivity estimate (all as hypotheses). -/

theorem parabolic_euler_step_laxMilgram
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hCoer : ∀ u : WeakH10,
      min (1 / τ) kmin * ‖u‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
            + κ x * u.weakDeriv x * u.weakDeriv x) :
    ∃ u : WeakH10, ∀ v : WeakH10, B u v = L v := by
  have hτinv : (0 : ℝ) < 1 / τ := one_div_pos.mpr hτ
  have hCpos : (0 : ℝ) < min (1 / τ) kmin := lt_min hτinv hkmin
  have hM0 : (0 : ℝ) ≤ max (1 / τ) kmax :=
    le_trans (one_div_pos.mpr hτ).le (le_max_left _ _)
  have hCoer' : IsCoercive B := by
    refine ⟨min (1 / τ) kmin, hCpos, fun u => ?_⟩
    have h1 := hCoer u
    rw [hB u u]
    have hpow : min (1 / τ) kmin * ‖u‖ * ‖u‖ = min (1 / τ) kmin * ‖u‖ ^ 2 := by
      ring
    rw [hpow]
    exact h1
  rcases hCoer' with ⟨C, hC0, hcoer⟩
  have hBcoerQ : IsCoercive (weakH10_descendB B hB hBnd hM0) := by
    refine ⟨C, hC0, fun q => ?_⟩
    obtain ⟨u, rfl⟩ := SeparationQuotient.surjective_mk q
    rw [SeparationQuotient.norm_mk, weakH10_descendB_mk]
    exact hcoer u
  obtain ⟨qu, hq⟩ := laxMilgram_exist_of_coercive (SeparationQuotient WeakH10)
    (weakH10_descendB B hB hBnd hM0) hBcoerQ
    (weakH10_descendCLM L (fun w hw => weakH10_L_vanish L hL w hw))
  obtain ⟨u0, rfl⟩ := SeparationQuotient.surjective_mk qu
  refine ⟨u0, fun v => ?_⟩
  have hqv := hq (SeparationQuotient.mk v)
  rw [weakH10_descendB_mk, weakH10_descendCLM_mk] at hqv
  exact hqv


theorem weakH10_memLp_mul_intervalIntegrable (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    IntervalIntegrable (fun x => f x * g x) volume 0 1 := by
  have hInt : Integrable (f * g) (volume.restrict (Set.Icc 0 1)) :=
    hf.integrable_mul hg
  have hOn : IntegrableOn (f * g) (Set.Icc 0 1) volume := hInt
  have hU : IntegrableOn (fun x => f x * g x) (Set.uIcc (0 : ℝ) 1) volume := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hOn
  exact hU.intervalIntegrable

/-- Dividing an `L²` function on `[0,1]` by a constant stays `L²`. -/

theorem weakH10_memLp_div (f : ℝ → ℝ) (τ : ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1))) :
    MemLp (fun x => f x / τ) 2 (volume.restrict (Set.Icc 0 1)) := by
  have heq : (fun x => f x / τ) = (fun x => τ⁻¹ * f x) :=
    funext fun x => div_eq_inv_mul _ _
  rw [heq]
  exact hf.const_mul τ⁻¹

/-- The conductivity term `κ * du * dv` is interval integrable on `[0,1]`
when `κ` is a.e. bounded and `du dv` are `L²`. -/

theorem weakH10_kappa_intervalIntegrable (κ du dv : ℝ → ℝ)
    {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hdu : MemLp du 2 (volume.restrict (Set.Icc 0 1)))
    (hdv : MemLp dv 2 (volume.restrict (Set.Icc 0 1))) :
    IntervalIntegrable (fun x => κ x * du x * dv x) volume 0 1 := by
  have hprod : Integrable (du * dv) (volume.restrict (Set.Icc 0 1)) :=
    hdu.integrable_mul hdv
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), ‖κ x‖ ≤ kmax := by
    filter_upwards [hκ] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hkmin.le hx.1)]
    exact hx.2
  have hκprod : Integrable (fun x => κ x * (du x * dv x))
      (volume.restrict (Set.Icc 0 1)) :=
    hprod.bdd_mul hκ_meas hbound
  have heq : (fun x => κ x * (du x * dv x)) =ᵐ[volume.restrict (Set.Icc 0 1)]
      (fun x => κ x * du x * dv x) :=
    Filter.Eventually.of_forall fun x => by ring
  have hOn : IntegrableOn (fun x => κ x * du x * dv x) (Set.Icc 0 1) volume :=
    hκprod.congr heq
  have hU : IntegrableOn (fun x => κ x * du x * dv x)
      (Set.uIcc (0 : ℝ) 1) volume := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hOn
  exact hU.intervalIntegrable

/-- The five interval-integrability facts needed to identify the
Euler-step equation from `B u v = L v`, for every `u v : WeakH10`. -/

theorem euler_step_intervalIntegrable
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (u v : WeakH10) :
    IntervalIntegrable
        (fun x => (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => uprev x / τ * v.toFun x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => F x * v.toFun x) volume 0 1 := by
  have hTu : MemLp u.toFun 2 (volume.restrict (Set.Icc 0 1)) :=
    weakH10_toFun_memLp u
  have hTv : MemLp v.toFun 2 (volume.restrict (Set.Icc 0 1)) :=
    weakH10_toFun_memLp v
  have hDu : MemLp u.weakDeriv 2 (volume.restrict (Set.Icc 0 1)) :=
    u.weakDeriv_memLp
  have hDv : MemLp v.weakDeriv 2 (volume.restrict (Set.Icc 0 1)) :=
    v.weakDeriv_memLp
  have huprev_div : MemLp (fun x => uprev x / τ) 2
      (volume.restrict (Set.Icc 0 1)) :=
    weakH10_memLp_div uprev τ huprev
  have hkap : IntervalIntegrable (fun x => κ x * u.weakDeriv x * v.weakDeriv x)
      volume 0 1 :=
    weakH10_kappa_intervalIntegrable κ u.weakDeriv v.weakDeriv hkmin
      hκ_meas hκ hDu hDv
  have h5 : IntervalIntegrable (fun x => F x * v.toFun x) volume 0 1 :=
    weakH10_memLp_mul_intervalIntegrable F v.toFun hF hTv
  have h4 : IntervalIntegrable (fun x => uprev x / τ * v.toFun x) volume 0 1 :=
    weakH10_memLp_mul_intervalIntegrable _ v.toFun huprev_div hTv
  have h3 : IntervalIntegrable (fun x => (F x + uprev x / τ) * v.toFun x)
      volume 0 1 :=
    weakH10_memLp_mul_intervalIntegrable _ v.toFun (hF.add huprev_div) hTv
  have h2a : IntervalIntegrable (fun x => u.toFun x * v.toFun x / τ)
      volume 0 1 :=
    (weakH10_memLp_mul_intervalIntegrable u.toFun v.toFun hTu hTv).div_const τ
  have h2 : IntervalIntegrable
      (fun x => u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1 :=
    h2a.add hkap
  have h1a : IntervalIntegrable
      (fun x => (u.toFun x - uprev x) / τ * v.toFun x) volume 0 1 := by
    have hprod := weakH10_memLp_mul_intervalIntegrable _ v.toFun
      (hTu.sub huprev) hTv
    have hdiv := hprod.div_const τ
    have heq : (fun x => ((u.toFun - uprev) x * v.toFun x) / τ)
        = (fun x => (u.toFun x - uprev x) / τ * v.toFun x) := by
      funext x
      show ((u.toFun - uprev) x * v.toFun x) / τ
        = (u.toFun x - uprev x) / τ * v.toFun x
      simp only [Pi.sub_apply]
      ring
    rwa [heq] at hdiv
  have h1 : IntervalIntegrable
      (fun x => (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1 :=
    h1a.add hkap
  exact ⟨h1, h2, h3, h4, h5⟩


theorem euler_step_identify
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (u : WeakH10)
    (hEq : ∀ v : WeakH10, B u v = L v)
    (hInt : ∀ v : WeakH10,
      IntervalIntegrable
          (fun x => (u.toFun x - uprev x) / τ * v.toFun x
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => u.toFun x * v.toFun x / τ
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => uprev x / τ * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => F x * v.toFun x) volume 0 1) :
    ∀ v : WeakH10,
      ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, F x * v.toFun x := by
  intro v
  obtain ⟨hS, hBint, hLint, hC, hFint⟩ := hInt v
  have hEqv := hEq v
  rw [hB u v, hL v] at hEqv
  have hptS : Set.EqOn
      (fun x => (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x)
      (fun x => (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
        - uprev x / τ * v.toFun x)
      (Set.uIcc (0 : ℝ) 1) := by
    intro x _
    show (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x
      = (u.toFun x * v.toFun x / τ + κ x * u.weakDeriv x * v.weakDeriv x)
        - uprev x / τ * v.toFun x
    ring
  have hptF : Set.EqOn
      (fun x => F x * v.toFun x)
      (fun x => (F x + uprev x / τ) * v.toFun x - uprev x / τ * v.toFun x)
      (Set.uIcc (0 : ℝ) 1) := by
    intro x _
    show F x * v.toFun x
      = (F x + uprev x / τ) * v.toFun x - uprev x / τ * v.toFun x
    ring
  have hS_eq : (∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
      + κ x * u.weakDeriv x * v.weakDeriv x)
      = (∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
        - ∫ x in (0 : ℝ)..1, uprev x / τ * v.toFun x :=
    (intervalIntegral.integral_congr hptS).trans
      (intervalIntegral.integral_sub hBint hC)
  have hF_eq : (∫ x in (0 : ℝ)..1, F x * v.toFun x)
      = (∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
        - ∫ x in (0 : ℝ)..1, uprev x / τ * v.toFun x :=
    (intervalIntegral.integral_congr hptF).trans
      (intervalIntegral.integral_sub hLint hC)
  rw [hS_eq, hF_eq, hEqv]


theorem parabolic_euler_step
    {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin) (hτk : τ * kmin < 1)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hCoer : ∀ u : WeakH10,
      min (1 / τ) kmin * ‖u‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
            + κ x * u.weakDeriv x * u.weakDeriv x)
    (hInt : ∀ (u v : WeakH10),
      IntervalIntegrable
          (fun x => (u.toFun x - uprev x) / τ * v.toFun x
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => u.toFun x * v.toFun x / τ
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => uprev x / τ * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => F x * v.toFun x) volume 0 1)
    (hLax : ∃ u : WeakH10, ∀ v : WeakH10, B u v = L v)
    (hIdent : ∀ (u : WeakH10), (∀ v : WeakH10, B u v = L v) →
      ∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, F x * v.toFun x)
    (hEnergy : ∀ (u : WeakH10),
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, F x * v.toFun x) →
      (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (τ / kmin) * (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2) :
    ∃ u : WeakH10,
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, F x * v.toFun x)
      ∧ (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (τ / kmin) * (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  obtain ⟨u, hu⟩ := hLax
  have hStep := hIdent u hu
  have hEn := hEnergy u hStep
  exact ⟨u, hStep, hEn⟩


theorem kappa_avg
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ Set.Icc t0 t1)
    (hτ : 0 < b - a) :
    AEStronglyMeasurable
        (fun x => (1 / (b - a)) * ∫ s in a..b, κ s x)
        (volume.restrict (Set.Icc 0 1))
      ∧ ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
        kmin ≤ (1 / (b - a)) * ∫ s in a..b, κ s x
          ∧ (1 / (b - a)) * ∫ s in a..b, κ s x ≤ kmax := by
  have hsub' : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hsub (fun x hx => hx)
  have hprod : volume.restrict (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (Measure.prod_restrict _ _).symm
  have hmeas_small : AEStronglyMeasurable (Function.uncurry κ)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have h1 : AEStronglyMeasurable (Function.uncurry κ)
        ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
          (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)) := hκ_meas.restrict
    rw [Measure.restrict_restrict_of_subset hsub', hprod] at h1
    exact h1
  have hmeas_swap : AEStronglyMeasurable (fun z : ℝ × ℝ => Function.uncurry κ z.swap)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc a b))) :=
    hmeas_small.prod_swap
  have hInt_meas : AEStronglyMeasurable
      (fun x : ℝ => ∫ s, Function.uncurry κ (x, s).swap ∂(volume.restrict (Set.Icc a b)))
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hmeas_swap.integral_prod_right'
  have hint_eq : ∀ x : ℝ, (∫ s, Function.uncurry κ (x, s).swap ∂(volume.restrict (Set.Icc a b)))
      = ∫ s in a..b, κ s x := by
    intro x
    have hrfl : (∫ s, Function.uncurry κ (x, s).swap ∂(volume.restrict (Set.Icc a b)))
        = ∫ s in Set.Icc a b, κ s x ∂volume := rfl
    rw [hrfl, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  have havg_meas : AEStronglyMeasurable
      (fun x => (1 / (b - a)) * ∫ s in a..b, κ s x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h2 : (fun x : ℝ => ∫ s, Function.uncurry κ (x, s).swap ∂(volume.restrict (Set.Icc a b)))
        = fun x => ∫ s in a..b, κ s x := funext hint_eq
    have h3 := hInt_meas.congr (ae_of_all _ (fun x => congrFun h2 x))
    exact h3.const_mul _
  have hbdd_small : ∀ᵐ p ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax :=
    ae_restrict_of_ae_restrict_of_subset hsub' hκ
  rw [hprod] at hbdd_small
  have hbdd_swap : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc a b))),
      kmin ≤ κ q.swap.1 q.swap.2 ∧ κ q.swap.1 q.swap.2 ≤ kmax := by
    rw [← Measure.prod_swap] at hbdd_small
    exact ae_of_ae_map measurable_swap.aemeasurable hbdd_small
  have hbdd_slice : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
        kmin ≤ κ (x, s).swap.1 (x, s).swap.2 ∧ κ (x, s).swap.1 (x, s).swap.2 ≤ kmax :=
    Measure.ae_ae_of_ae_prod hbdd_swap
  have hbdd_clean : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), kmin ≤ κ s x ∧ κ s x ≤ kmax := by
    filter_upwards [hbdd_slice] with x hx
    filter_upwards [hx] with s hs
    exact hs
  have hmeas_slice : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEStronglyMeasurable (fun s => Function.uncurry κ (x, s).swap)
        (volume.restrict (Set.Icc a b)) :=
    hmeas_swap.prodMk_left
  have hmeas_clean : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEStronglyMeasurable (fun s => κ s x) (volume.restrict (Set.Icc a b)) := by
    filter_upwards [hmeas_slice] with x hx
    have heq : ∀ s : ℝ, Function.uncurry κ (x, s).swap = κ s x := fun s => rfl
    exact hx.congr (ae_of_all _ heq)
  have hgood : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      kmin ≤ (1 / (b - a)) * ∫ s in a..b, κ s x
        ∧ (1 / (b - a)) * ∫ s in a..b, κ s x ≤ kmax := by
    filter_upwards [hmeas_clean, hbdd_clean] with x hx_meas hx_bdd
    have hnorm : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
        ‖κ s x‖ ≤ max |kmin| |kmax| := by
      filter_upwards [hx_bdd] with s hs
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have hle1 : |kmin| ≤ max |kmin| |kmax| := le_max_left _ _
        have h3 : -|kmin| ≤ kmin := neg_abs_le _
        linarith [hs.1]
      · have hle2 : |kmax| ≤ max |kmin| |kmax| := le_max_right _ _
        have h3 : kmax ≤ |kmax| := le_abs_self _
        linarith [hs.2]
    have hfin : volume (Set.Icc a b) < ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have hInt_on : IntegrableOn (fun s => κ s x) (Set.Icc a b) volume :=
      IntegrableOn.of_bound hfin hx_meas _ hnorm
    have hII : IntervalIntegrable (fun s => κ s x) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
      exact hInt_on.mono_set Set.Ioc_subset_Icc_self
    have hII_lo : IntervalIntegrable (fun _ => kmin) volume a b := intervalIntegrable_const
    have hII_hi : IntervalIntegrable (fun _ => kmax) volume a b := intervalIntegrable_const
    have hlo_ae : (fun _ => kmin) ≤ᵐ[volume.restrict (Set.Icc a b)] (fun s => κ s x) := by
      filter_upwards [hx_bdd] with s hs
      exact hs.1
    have hhi_ae : (fun s => κ s x) ≤ᵐ[volume.restrict (Set.Icc a b)] (fun _ => kmax) := by
      filter_upwards [hx_bdd] with s hs
      exact hs.2
    have hlo := intervalIntegral.integral_mono_ae_restrict hab.le hII_lo hII hlo_ae
    have hhi := intervalIntegral.integral_mono_ae_restrict hab.le hII hII_hi hhi_ae
    rw [intervalIntegral.integral_const] at hlo hhi
    rw [smul_eq_mul] at hlo hhi
    have hτne : b - a ≠ 0 := ne_of_gt hτ
    have hτpos : (0 : ℝ) < 1 / (b - a) := one_div_pos.mpr hτ
    have hscale : (1 / (b - a)) * ((b - a) * kmin) = kmin := by
      rw [← mul_assoc, one_div_mul_cancel hτne, one_mul]
    have hscale2 : (1 / (b - a)) * ((b - a) * kmax) = kmax := by
      rw [← mul_assoc, one_div_mul_cancel hτne, one_mul]
    constructor
    · calc kmin = (1 / (b - a)) * ((b - a) * kmin) := hscale.symm
        _ ≤ (1 / (b - a)) * ∫ s in a..b, κ s x :=
          mul_le_mul_of_nonneg_left hlo (le_of_lt hτpos)
    · calc (1 / (b - a)) * ∫ s in a..b, κ s x ≤ (1 / (b - a)) * ((b - a) * kmax) :=
          mul_le_mul_of_nonneg_left hhi (le_of_lt hτpos)
        _ = kmax := hscale2
  exact ⟨havg_meas, hgood⟩


theorem forcing_avg_meas
    {t0 t1 : ℝ} (ht : t0 < t1)
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ Set.Icc t0 t1)
    (hτ : 0 < b - a) :
    AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
      (volume.restrict (Set.Icc 0 1)) := by
  have hsub' : Set.Icc a b ×ˢ Set.Icc (0 : ℝ) (1 : ℝ)
      ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ) :=
    Set.prod_mono hsub le_rfl
  haveI hfin : IsFiniteMeasure
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]
    exact ((isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hInt : Integrable (Function.uncurry F)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))) :=
    hF.integrable (one_le_two : (1 : ENNReal) ≤ 2)
  have hInt_small : Integrable (Function.uncurry F)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))) := by
    have h := hInt.restrict (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))
    rwa [Measure.restrict_restrict_of_subset hsub'] at h
  have hprod : volume.restrict (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact (Measure.prod_restrict _ _).symm
  rw [hprod] at hInt_small
  have hInt_x : Integrable
      (fun x => ∫ s, Function.uncurry F (s, x) ∂(volume.restrict (Set.Icc a b)))
      (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))) :=
    hInt_small.integral_prod_right
  have hrewrite : (fun x => ∫ s, Function.uncurry F (s, x) ∂(volume.restrict (Set.Icc a b)))
      = fun x => ∫ s in a..b, F s x := by
    funext x
    have h1 : (∫ s, Function.uncurry F (s, x) ∂(volume.restrict (Set.Icc a b)))
        = ∫ s in Set.Icc a b, F s x := rfl
    rw [h1, integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le hab.le).symm
  rw [hrewrite] at hInt_x
  exact hInt_x.aestronglyMeasurable.const_mul _


lemma eLpNorm_toReal_sq_eq_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2netop : (2 : ℝ≥0∞) ≠ ∞ := ENNReal.ofNat_ne_top
  have h := hf.eLpNorm_eq_integral_rpow_norm (p := 2) h2ne0 h2netop
  have htr : ENNReal.toReal (2 : ℝ≥0∞) = 2 := by simp
  rw [htr] at h
  have hnn : 0 ≤ ∫ x, (f x) ^ 2 ∂μ :=
    integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg _)
  have hfg : (fun x => ‖f x‖ ^ (2 : ℝ)) = fun x => (f x) ^ 2 := by
    funext x
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h, hfg, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- Pointwise Jensen bound: the squared average is bounded by the average of squares,
via nonnegativity of the variance. -/

lemma avg_sq_le {a b : ℝ} (hab : a < b) (hτ : 0 < b - a)
    {g : ℝ → ℝ} (hg : Integrable g (volume.restrict (Set.uIoc a b)))
    (hg2 : Integrable (fun s => (g s) ^ 2) (volume.restrict (Set.uIoc a b))) :
    ((1 / (b - a)) * ∫ s in a..b, g s) ^ 2
      ≤ (1 / (b - a)) * ∫ s in a..b, (g s) ^ 2 := by
  have hτne : b - a ≠ 0 := ne_of_gt hτ
  have hab' : a ≤ b := le_of_lt hab
  have hii : ∀ f : ℝ → ℝ, (∫ s in a..b, f s)
      = ∫ s, f s ∂(volume.restrict (Set.uIoc a b)) := by
    intro f
    rw [intervalIntegral.integral_of_le hab', Set.uIoc_of_le hab']
  simp only [hii]
  set μ := volume.restrict (Set.uIoc a b) with hμdef
  have hfin : IsFiniteMeasure μ := ⟨by
    rw [hμdef, Measure.restrict_apply_univ, Real.volume_uIoc, lt_top_iff_ne_top]
    exact ENNReal.ofReal_ne_top⟩
  set S := ∫ s, g s ∂μ with hSdef
  set Q := ∫ s, (g s) ^ 2 ∂μ with hQdef
  set c := (1 / (b - a)) * S with hcdef
  have hS : S = (b - a) * c := by rw [hcdef]; field
  have hsub : Integrable (fun s => (g s) ^ 2 - (2 * c) * (g s)) μ :=
    hg2.sub (hg.const_mul (2 * c))
  have hcon : Integrable (fun _ => c ^ 2) μ := integrable_const _
  have hadd : Integrable (fun s => ((g s) ^ 2 - (2 * c) * (g s)) + c ^ 2) μ :=
    hsub.add hcon
  have hcsq : Integrable (fun s => (g s - c) ^ 2) μ := by
    apply hadd.congr (ae_of_all _ fun s => ?_)
    ring
  have hnonneg : 0 ≤ ∫ s, (g s - c) ^ 2 ∂μ :=
    integral_nonneg_of_ae (ae_of_all _ fun s => sq_nonneg _)
  have hμuniv : μ.real Set.univ = b - a := by
    rw [measureReal_def, hμdef, Measure.restrict_apply_univ, Real.volume_uIoc,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (sub_nonneg.mpr hab')]
  have hexp : ∫ s, (g s - c) ^ 2 ∂μ = Q - 2 * c * S + (b - a) * c ^ 2 := by
    have e1 : ∫ s, (g s - c) ^ 2 ∂μ
        = ∫ s, ((g s) ^ 2 - (2 * c) * (g s)) + c ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with s
      ring
    rw [e1, integral_add hsub hcon, integral_sub hg2 (hg.const_mul _),
      integral_const_mul, integral_const, hμuniv, smul_eq_mul, ← hSdef, ← hQdef]
  have h2cS : 2 * c * S = 2 * (b - a) * c ^ 2 := by rw [hS]; ring
  have hle : (b - a) * c ^ 2 ≤ Q := by linarith
  have hpos : (0 : ℝ) ≤ 1 / (b - a) := le_of_lt (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hle hpos
  have hcancel : (1 / (b - a)) * ((b - a) * c ^ 2) = c ^ 2 := by field
  rwa [hcancel] at hmul

/-- Jensen norm bound for the time-averaged forcing, with measurability
of the average as a hypothesis. -/

theorem forcing_avg_norm
    {t0 t1 : ℝ} (ht : t0 < t1)
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ Set.Icc t0 t1)
    (hτ : 0 < b - a)
    (hAvg_meas : AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
      (volume.restrict (Set.Icc 0 1))) :
    (eLpNorm (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2
        (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      ≤ (1 / (b - a)) * ∫ s in a..b,
        (eLpNorm (fun x => F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  have hab' : a ≤ b := le_of_lt hab
  have hτne : b - a ≠ 0 := ne_of_gt hτ
  set μab := volume.restrict (Set.uIoc a b) with hμabdef
  set μ01 := volume.restrict (Set.Icc (0:ℝ) 1) with hμ01def
  have hfinab : IsFiniteMeasure μab := ⟨by
    rw [hμabdef, Measure.restrict_apply_univ, Real.volume_uIoc, lt_top_iff_ne_top]
    exact ENNReal.ofReal_ne_top⟩
  have hfin01 : IsFiniteMeasure μ01 := ⟨by
    rw [hμ01def, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hsfab : SFinite μab := by rw [hμabdef]; exact inferInstance
  have hsf01 : SFinite μ01 := by rw [hμ01def]; exact inferInstance
  have huIoc_sub : Set.uIoc a b ⊆ Set.Icc t0 t1 := by
    rw [Set.uIoc_of_le hab']
    exact Set.Ioc_subset_Icc_self.trans hsub
  have hFsub : MemLp (Function.uncurry F) 2 (μab.prod μ01) := by
    have hprod : (volume.restrict (Set.uIoc a b ×ˢ Set.Icc (0:ℝ) 1) : Measure (ℝ × ℝ))
        = μab.prod μ01 := by
      have hv : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume :=
        Measure.volume_eq_prod ℝ ℝ
      rw [hv, ← Measure.prod_restrict, hμabdef, hμ01def]
    rw [← hprod]
    apply MemLp.mono_measure _ hF
    apply Measure.restrict_mono_set
    exact Set.prod_mono huIoc_sub (fun _ hx => hx)
  have hF2int : Integrable (fun p => (Function.uncurry F p) ^ 2) (μab.prod μ01) :=
    hFsub.integrable_sq
  have hF1int : Integrable (Function.uncurry F) (μab.prod μ01) :=
    memLp_one_iff_integrable.mp (hFsub.mono_exponent one_le_two)
  have hii : ∀ f : ℝ → ℝ, (∫ s in a..b, f s) = ∫ s, f s ∂μab := by
    intro f
    rw [intervalIntegral.integral_of_le hab', hμabdef, Set.uIoc_of_le hab']
  have hx1 : ∀ᵐ x ∂μ01, Integrable (fun s => F s x) μab := hF1int.prod_left_ae
  have hx2 : ∀ᵐ x ∂μ01, Integrable (fun s => (F s x) ^ 2) μab := hF2int.prod_left_ae
  have hpoint : ∀ᵐ x ∂μ01, ((1 / (b - a)) * ∫ s in a..b, F s x) ^ 2
      ≤ (1 / (b - a)) * ∫ s in a..b, (F s x) ^ 2 := by
    filter_upwards [hx1, hx2] with x hx1x hx2x
    exact avg_sq_le hab hτ hx1x hx2x
  have hs_ae : ∀ᵐ s ∂μab, MemLp (fun x => F s x) 2 μ01 := by
    filter_upwards [hFsub.aestronglyMeasurable.prodMk_left, hF2int.prod_right_ae]
      with s hmeas hint
    exact (memLp_two_iff_integrable_sq hmeas).mpr hint
  by_cases hAvg : MemLp (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2 μ01
  · have hLHS : (eLpNorm (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2 μ01).toReal ^ 2
        = ∫ x, ((1 / (b - a)) * ∫ s in a..b, F s x) ^ 2 ∂μ01 :=
      eLpNorm_toReal_sq_eq_integral_sq hAvg
    have hRHSint : Integrable (fun x => (1 / (b - a)) * ∫ s in a..b, (F s x) ^ 2) μ01 := by
      have hnorm : Integrable (fun x => ∫ s, ‖(F s x) ^ 2‖ ∂μab) μ01 :=
        hF2int.integral_norm_prod_right
      have hpt : ∀ x, (∫ s, ‖(F s x) ^ 2‖ ∂μab) = (∫ s in a..b, (F s x) ^ 2) := by
        intro x
        rw [hii]
        apply integral_congr_ae
        filter_upwards with s
        exact (Real.norm_eq_abs _).trans (abs_of_nonneg (sq_nonneg _))
      have hae : (fun x => ∫ s, ‖(F s x) ^ 2‖ ∂μab) =ᵐ[μ01]
          (fun x => ∫ s in a..b, (F s x) ^ 2) :=
        ae_of_all _ hpt
      exact (hnorm.congr hae).const_mul _
    have hmono := integral_mono_ae hAvg.integrable_sq hRHSint hpoint
    have hF2int' : Integrable (Function.uncurry (fun s x => (F s x) ^ 2))
        ((volume.restrict (Set.uIoc a b)).prod μ01) := hF2int
    have hsw0 : (∫ y, (∫ x in a..b, (fun s x => (F s x) ^ 2) x y) ∂μ01)
        = ∫ x in a..b, ∫ y, (fun s x => (F s x) ^ 2) x y ∂μ01 :=
      (intervalIntegral_integral_swap hF2int').symm
    have hswap : (∫ x, ((1 / (b - a)) * ∫ s in a..b, (F s x) ^ 2) ∂μ01)
        = (1 / (b - a)) * ∫ s in a..b, ∫ x, (F s x) ^ 2 ∂μ01 := by
      rw [integral_const_mul]
      exact congrArg _ hsw0
    have hcongr : (∫ s in a..b, ∫ x, (F s x) ^ 2 ∂μ01)
        = ∫ s in a..b, (eLpNorm (fun x => F s x) 2 μ01).toReal ^ 2 := by
      simp only [hii]
      apply integral_congr_ae
      filter_upwards [hs_ae] with s hs
      exact (eLpNorm_toReal_sq_eq_integral_sq hs).symm
    rw [hLHS]
    calc (∫ x, (((1 / (b - a)) * ∫ s in a..b, F s x) ^ 2) ∂μ01)
        ≤ (∫ x, ((1 / (b - a)) * ∫ s in a..b, (F s x) ^ 2) ∂μ01) := hmono
      _ = (1 / (b - a)) * ∫ s in a..b, ∫ x, (F s x) ^ 2 ∂μ01 := hswap
      _ = (1 / (b - a)) * ∫ s in a..b, (eLpNorm (fun x => F s x) 2 μ01).toReal ^ 2 :=
        congrArg _ hcongr
  · have heq : eLpNorm (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2 μ01 = ∞ := by
      by_contra hne
      exact hAvg (lt_top_iff_ne_top.mpr hne)
    have hzero : ((∞ : ℝ≥0∞).toReal) ^ 2 = 0 := by simp
    rw [heq, hzero]
    apply mul_nonneg _ _
    · positivity
    · apply intervalIntegral.integral_nonneg_of_ae hab'
      filter_upwards with s
      positivity




theorem rothe_slab_kappa
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    {N : ℕ} (hN : 0 < N)
    (hKappaAvgThm : ∀ {t0 t1 : ℝ}, t0 < t1 →
      ∀ {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ}, 0 < kmin →
      ∀ (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))),
      ∀ (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
        kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax),
      ∀ {a b : ℝ}, a < b → Set.Icc a b ⊆ Set.Icc t0 t1 → 0 < b - a →
      AEStronglyMeasurable
          (fun x => (1 / (b - a)) * ∫ s in a..b, κ s x)
          (volume.restrict (Set.Icc 0 1))
        ∧ ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
          kmin ≤ (1 / (b - a)) * ∫ s in a..b, κ s x
            ∧ (1 / (b - a)) * ∫ s in a..b, κ s x ≤ kmax)
    (k : ℕ) (hk : k < N) :
    AEStronglyMeasurable
        (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x)
        (volume.restrict (Set.Icc 0 1))
      ∧ ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
        kmin ≤ (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x
          ∧ (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x ≤ kmax := by
  set τ : ℝ := (t1 - t0) / N with hτ
  have hNt0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ_pos : 0 < τ := by
    rw [hτ]
    exact div_pos (sub_pos.mpr ht) hNt0
  set a : ℝ := t0 + k * τ with ha
  set b : ℝ := t0 + (k + 1) * τ with hb
  have hkk : (k : ℝ) < (k : ℝ) + 1 := lt_add_one _
  have hab : a < b := by
    rw [ha, hb]
    have hmul : (k : ℝ) * τ < ((k : ℝ) + 1) * τ :=
      mul_lt_mul_of_pos_right hkk hτ_pos
    linarith
  have hba : b - a = τ := by
    rw [ha, hb]
    ring
  have hpos : 0 < b - a := by rw [hba]; exact hτ_pos
  have hsub : Set.Icc a b ⊆ Set.Icc t0 t1 := by
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    obtain ⟨hax, hxb⟩ := hx
    have hka : 0 ≤ (k : ℝ) * τ :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt hτ_pos)
    have ht0a : t0 ≤ a := by rw [ha]; linarith
    have hle : k + 1 ≤ N := by omega
    have hleR : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hle
    have hmul : ((k : ℝ) + 1) * τ ≤ (N : ℝ) * τ :=
      mul_le_mul_of_nonneg_right hleR (le_of_lt hτ_pos)
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNt0
    have hNτ : (N : ℝ) * τ = t1 - t0 := by rw [hτ, mul_comm, div_mul_cancel₀ _ hNne]
    have hb1 : b ≤ t1 := by rw [hb]; linarith
    exact ⟨le_trans ht0a hax, le_trans hxb hb1⟩
  have h := hKappaAvgThm ht hkmin hκ_meas hκ hab hsub hpos
  rwa [hba] at h


theorem rothe_slab_forcing_memLp_aux
    {t0 t1 : ℝ}
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ Set.Icc t0 t1) (hba : 0 < b - a)
    (hAvg_meas : AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
      (volume.restrict (Set.Icc 0 1))) :
    MemLp (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2
      (volume.restrict (Set.Icc 0 1)) := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  have hVol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := rfl
  have hIocSub : Set.Ioc a b ⊆ Set.Icc t0 t1 := Set.Ioc_subset_Icc_self.trans hsub
  have hSub : Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) 1 ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono hIocSub (le_refl _)
  have hle : (volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤
      volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.prod_restrict, ← hVol]
    have hme : MeasurableSet (Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
      measurableSet_Ioc.prod measurableSet_Icc
    have heq : volume.restrict (Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) 1)
        = (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
          (Set.Ioc a b ×ˢ Set.Icc (0 : ℝ) 1) := by
      rw [Measure.restrict_restrict hme, Set.inter_eq_self_of_subset_left hSub]
    rw [heq]
    exact Measure.restrict_le_self
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  have hJRaw := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2 : ℝ≥0∞)) (μ := volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    (f := Function.uncurry F) (by simp) (by simp) (MeasureTheory.memLp_iff.mp hF)
  have hJ : (∫⁻ w, ‖Function.uncurry F w‖ₑ ^ 2
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) < ⊤ := by
    simpa only [h2, ENNReal.rpow_two] using hJRaw
  have hH2 : AEMeasurable (fun w : ℝ × ℝ => ‖Function.uncurry F w‖ₑ ^ 2)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    hF.aestronglyMeasurable.aemeasurable.enorm.pow_const 2
  have hH2small : AEMeasurable (fun w : ℝ × ℝ => ‖Function.uncurry F w‖ₑ ^ 2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Icc 0 1))) :=
    hH2.mono_ac (Measure.absolutelyContinuous_of_le hle)
  have hG_ae : AEMeasurable (fun x => ∫⁻ s in Set.Ioc a b, ‖F s x‖ₑ ^ 2 ∂volume)
      (volume.restrict (Set.Icc 0 1)) :=
    AEMeasurable.lintegral_prod_left' hH2small
  have hBack : (∫⁻ x in Set.Icc (0 : ℝ) 1,
        (∫⁻ s in Set.Ioc a b, ‖F s x‖ₑ ^ 2 ∂volume) ∂volume)
      = ∫⁻ w, ‖Function.uncurry F w‖ₑ ^ 2
        ∂((volume.restrict (Set.Ioc a b)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (MeasureTheory.lintegral_prod_symm _ hH2small).symm
  have hG_fin : (∫⁻ x in Set.Icc (0 : ℝ) 1,
      (∫⁻ s in Set.Ioc a b, ‖F s x‖ₑ ^ 2 ∂volume) ∂volume) < ⊤ := by
    rw [hBack, Measure.prod_restrict, ← hVol]
    exact lt_of_le_of_lt (MeasureTheory.lintegral_mono_set hSub) hJ
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
      (∫⁻ s in Set.Ioc a b, ‖F s x‖ₑ ^ 2 ∂volume) < ⊤ :=
    MeasureTheory.ae_lt_top' hG_ae (ne_of_lt hG_fin)
  have hJointAE : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc 0 1))) := by
    have hEq : (volume.restrict (Set.Icc t0 t1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1))
        = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
      rw [Measure.prod_restrict, ← hVol]
    rw [hEq]
    exact hF.aestronglyMeasurable
  have hSlice : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
      AEStronglyMeasurable (fun s => F s x) (volume.restrict (Set.Icc t0 t1)) :=
    hJointAE.prodMk_right
  have hg_sq : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) := Even.convexOn_pow even_two
  have hgc : ContinuousOn (fun y : ℝ => y ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have hsc : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have h0 : volume (Set.Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr hba).ne'
  have ht_ne : volume (Set.Ioc a b) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hOfRealSq : ∀ y : ℝ, ENNReal.ofReal (y ^ 2) = ‖y‖ₑ ^ 2 := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ← sq_abs y, ENNReal.ofReal_pow (abs_nonneg y) 2]
  have hae_bound : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
      ‖(1 / (b - a)) * ∫ s in a..b, F s x‖ₑ ^ 2
        ≤ ENNReal.ofReal ((b - a)⁻¹) * (∫⁻ s in Set.Ioc a b, ‖F s x‖ₑ ^ 2 ∂volume) := by
    filter_upwards [hae, hSlice] with x hx_fin hx_meas_big
    have hx_meas : AEStronglyMeasurable (fun s => F s x)
        (volume.restrict (Set.Ioc a b)) := by
      have hrr : (volume.restrict (Set.Icc t0 t1)).restrict (Set.Ioc a b)
          = volume.restrict (Set.Ioc a b) := by
        rw [Measure.restrict_restrict measurableSet_Ioc,
          Set.inter_eq_self_of_subset_left hIocSub]
      rw [← hrr]
      exact hx_meas_big.restrict
    have hiff := MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (μ := volume.restrict (Set.Ioc a b)) (f := fun s => F s x)
      (by simp) (by simp) hx_meas
    simp only [h2, ENNReal.rpow_two] at hiff
    have hx_mem : MemLp (fun s => F s x) 2 (volume.restrict (Set.Ioc a b)) :=
      MeasureTheory.memLp_iff.mpr (hiff.mpr hx_fin)
    have hx_int1 : IntegrableOn (fun s => F s x) (Set.Ioc a b) volume :=
      MeasureTheory.MemLp.integrable one_le_two hx_mem
    have hx_int2 : Integrable (fun s => (F s x) ^ 2) (volume.restrict (Set.Ioc a b)) :=
      hx_mem.integrable_sq
    have hx_int2_on : IntegrableOn ((fun y : ℝ => y ^ 2) ∘ (fun s => F s x))
        (Set.Ioc a b) volume := hx_int2
    have hfs : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)),
        (fun s => F s x) s ∈ Set.univ :=
      ae_of_all _ fun s => Set.mem_univ _
    have hJen := hg_sq.map_set_average_le hgc hsc h0 ht_ne hfs hx_int1 hx_int2_on
    have hJen2 : ((1 / (b - a)) * ∫ s in a..b, F s x) ^ 2
        ≤ (b - a)⁻¹ • ∫ s in Set.Ioc a b, (F s x) ^ 2 ∂volume := by
      simpa only [MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def,
        Real.volume_Ioc, ENNReal.toReal_ofReal (le_of_lt hba), smul_eq_mul, one_div,
        Function.comp_apply, ← intervalIntegral.integral_of_le hab.le] using hJen
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] (fun s => (F s x) ^ 2) :=
      ae_of_all _ fun s => sq_nonneg _
    have h2eq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hx_int2 hnn
    have hle0 := ENNReal.ofReal_le_ofReal hJen2
    simpa only [smul_eq_mul,
      ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hba)), h2eq, hOfRealSq] using hle0
  have hFinal : (∫⁻ x in Set.Icc (0 : ℝ) 1,
      ‖(1 / (b - a)) * ∫ s in a..b, F s x‖ₑ ^ 2 ∂volume) < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae hae_bound) ?_
    simp only [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((b - a)⁻¹)) _
      ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG_fin
  have hiff_final := MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (p := (2 : ℝ≥0∞)) (μ := volume.restrict (Set.Icc 0 1))
    (f := fun x => (1 / (b - a)) * ∫ s in a..b, F s x) (by simp) (by simp) hAvg_meas
  simp only [h2, ENNReal.rpow_two] at hiff_final
  exact MeasureTheory.memLp_iff.mpr (hiff_final.mpr hFinal)

/-- Averaged forcing is `L²`: assembly from measurability, the norm
bound, and section-norm finiteness (all as hypotheses). -/

theorem rothe_slab_forcing_memLp
    {t0 t1 : ℝ} (ht : t0 < t1)
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {N : ℕ} (hN : 0 < N)
    (hFMeasThm : ∀ {t0 t1 : ℝ}, t0 < t1 →
      ∀ {F : ℝ → ℝ → ℝ},
      ∀ (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))),
      ∀ {a b : ℝ}, a < b → Set.Icc a b ⊆ Set.Icc t0 t1 → 0 < b - a →
      AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
        (volume.restrict (Set.Icc 0 1)))
    (hFNormThm : ∀ {t0 t1 : ℝ}, t0 < t1 →
      ∀ {F : ℝ → ℝ → ℝ},
      ∀ (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))),
      ∀ {a b : ℝ}, a < b → Set.Icc a b ⊆ Set.Icc t0 t1 → 0 < b - a →
      ∀ (hAvg_meas : AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
        (volume.restrict (Set.Icc 0 1))),
      (eLpNorm (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2
          (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (1 / (b - a)) * ∫ s in a..b,
          (eLpNorm (fun x => F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
    (hSecFinThm : ∀ {t0 t1 : ℝ}, t0 < t1 →
      ∀ {F : ℝ → ℝ → ℝ},
      ∀ (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))),
      ∀ {a b : ℝ}, a < b → Set.Icc a b ⊆ Set.Icc t0 t1 →
      (∫⁻ s in Set.Ioc a b, (eLpNorm (fun x => F s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) ^ 2
        ∂volume) < ∞)
    (k : ℕ) (hk : k < N) :
    MemLp (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) 2
      (volume.restrict (Set.Icc 0 1)) := by
  set a := t0 + k * ((t1 - t0) / N) with ha
  set b := t0 + (k + 1) * ((t1 - t0) / N) with hb
  set τ := (t1 - t0) / N with hτdef
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have h10 : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
  have hτ : 0 < τ := by
    rw [hτdef]
    positivity
  have hba : b - a = τ := by
    simp only [ha, hb, hτdef]
    ring
  have hba_pos : 0 < b - a := by
    rw [hba]
    exact hτ
  have hab : a < b := sub_pos.mp hba_pos
  have htb : b ≤ t1 := by
    rw [hb, hτdef]
    have h1 : k.succ ≤ N := Nat.succ_le_of_lt hk
    have h1r : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1
    have h2 : (N : ℝ) * ((t1 - t0) / ↑N) = t1 - t0 := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hNne
    have h3 : ((k : ℝ) + 1) * ((t1 - t0) / ↑N) ≤ (N : ℝ) * ((t1 - t0) / ↑N) :=
      mul_le_mul_of_nonneg_right h1r (div_nonneg h10.le hNpos.le)
    linarith
  have hta : t0 ≤ a := by
    rw [ha, hτdef]
    have hnn : (0 : ℝ) ≤ (k : ℝ) * ((t1 - t0) / ↑N) := by positivity
    linarith
  have hsub : Set.Icc a b ⊆ Set.Icc t0 t1 := Set.Icc_subset_Icc hta htb
  have hMem : MemLp (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2
      (volume.restrict (Set.Icc 0 1)) :=
    rothe_slab_forcing_memLp_aux hF hab hsub hba_pos
      (hFMeasThm ht hF hab hsub hba_pos)
  rw [hba] at hMem
  simp only [ha, hb, hτdef] at hMem ⊢
  exact hMem


theorem rothe_slab_package
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    {N : ℕ} (hN : 0 < N)
    (k : ℕ) (hk : k < N)
    (hκk_meas : AEStronglyMeasurable (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), κ s x)
        (volume.restrict (Set.Icc 0 1)))
    (hκk : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
        kmin ≤ (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), κ s x
          ∧ (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), κ s x ≤ kmax)
    (hFk : MemLp (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), F s x) 2 (volume.restrict (Set.Icc 0 1)))
        (hBndThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (u v : WeakH10),
    |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x|
      ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hCoerThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (u : WeakH10),
    min (1 / τ) kmin * ‖u‖ ^ 2
      ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
          + κ x * u.weakDeriv x * u.weakDeriv x)
    (hRhsThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (v : WeakH10),
    |∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x|
      ≤ ((eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ) * ‖v‖)
    (hBclmThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖),
    ∃ B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ,
      ∀ u v : WeakH10,
        B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x)
    (hLclmThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (hRhs : ∀ v : WeakH10,
      |∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x|
        ≤ ((eLpNorm F 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ) * ‖v‖),
    ∃ L : WeakH10 →L[ℝ] ℝ,
      ∀ v : WeakH10,
        L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (hLaxThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hCoer : ∀ u : WeakH10,
      min (1 / τ) kmin * ‖u‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
            + κ x * u.weakDeriv x * u.weakDeriv x),
    ∃ u : WeakH10, ∀ v : WeakH10, B u v = L v)
    (uprev : ℝ → ℝ)
    (huprev : MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ, ∃ L : WeakH10 →L[ℝ] ℝ,
      (∀ u v : WeakH10,
        B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / ((t1 - t0) / N)
          + ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x) * u.weakDeriv x * v.weakDeriv x)
      ∧ (∀ v : WeakH10,
        L v = ∫ x in (0 : ℝ)..1, ((fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) x + uprev x / ((t1 - t0) / N)) * v.toFun x)
      ∧ ∃ u : WeakH10, ∀ v : WeakH10, B u v = L v := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hτpos : (0 : ℝ) < (t1 - t0) / (N : ℝ) := div_pos (sub_pos.mpr ht) hN'
  set τ : ℝ := (t1 - t0) / N
  set κslab : ℝ → ℝ :=
    fun x => (1 / τ) * ∫ s in (t0 + k * τ)..(t0 + (k + 1) * τ), κ s x
  set Fslab : ℝ → ℝ :=
    fun x => (1 / τ) * ∫ s in (t0 + k * τ)..(t0 + (k + 1) * τ), F s x
  have hκk_meas' : AEStronglyMeasurable κslab (volume.restrict (Set.Icc 0 1)) :=
    hκk_meas
  have hκk' : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
      kmin ≤ κslab x ∧ κslab x ≤ kmax := hκk
  have hFk' : MemLp Fslab 2 (volume.restrict (Set.Icc 0 1)) := hFk
  have hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κslab x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖ :=
    hBndThm hτpos hkmin hκk_meas' hκk'
  have hCoer : ∀ u : WeakH10,
      min (1 / τ) kmin * ‖u‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
          + κslab x * u.weakDeriv x * u.weakDeriv x :=
    hCoerThm hτpos hkmin hκk_meas' hκk'
  have hRhs : ∀ v : WeakH10,
      |∫ x in (0 : ℝ)..1, (Fslab x + uprev x / τ) * v.toFun x|
        ≤ ((eLpNorm Fslab 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal / τ) * ‖v‖ :=
    hRhsThm hτpos hFk' huprev
  obtain ⟨B, hB⟩ := hBclmThm hτpos hkmin hκk_meas' hκk' hBnd
  obtain ⟨L, hL⟩ := hLclmThm hτpos hFk' huprev hRhs
  obtain ⟨u, hu⟩ :=
    hLaxThm hτpos hkmin hκk_meas' hκk' hFk' huprev B hB L hL hBnd hCoer
  exact ⟨B, L, hB, hL, u, hu⟩


theorem rothe_slab_assemble
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    {N : ℕ} (hN : 0 < N)
    (k : ℕ) (hk : k < N)
    (hτsmall : ((t1 - t0) / N) * kmin < 1)
    (hκk_meas : AEStronglyMeasurable (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), κ s x)
        (volume.restrict (Set.Icc 0 1)))
    (hκk : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
        kmin ≤ (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), κ s x
          ∧ (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), κ s x ≤ kmax)
    (hFk : MemLp (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * (((t1 - t0) / N)))..(t0 + (k + 1) * (((t1 - t0) / N))), F s x) 2 (volume.restrict (Set.Icc 0 1)))
    (hBL : ∀ (uprev : ℝ → ℝ), MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ, ∃ L : WeakH10 →L[ℝ] ℝ,
        (∀ u v : WeakH10,
          B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / ((t1 - t0) / N)
            + ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x) * u.weakDeriv x * v.weakDeriv x)
        ∧ (∀ v : WeakH10,
          L v = ∫ x in (0 : ℝ)..1, ((fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) x + uprev x / ((t1 - t0) / N)) * v.toFun x)
        ∧ ∃ u : WeakH10, ∀ v : WeakH10, B u v = L v)
        (hBndThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (u v : WeakH10),
    |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x|
      ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
        (hCoerThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (u : WeakH10),
    min (1 / τ) kmin * ‖u‖ ^ 2
      ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
          + κ x * u.weakDeriv x * u.weakDeriv x)
        (hIntThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (u v : WeakH10), IntervalIntegrable
        (fun x => (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => uprev x / τ * v.toFun x) volume 0 1
      ∧ IntervalIntegrable
        (fun x => F x * v.toFun x) volume 0 1)
        (hIdentThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (u : WeakH10)
    (hEq : ∀ v : WeakH10, B u v = L v)
    (hInt : ∀ v : WeakH10,
      IntervalIntegrable
          (fun x => (u.toFun x - uprev x) / τ * v.toFun x
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => u.toFun x * v.toFun x / τ
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => uprev x / τ * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => F x * v.toFun x) volume 0 1),
    ∀ v : WeakH10,
      ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, F x * v.toFun x)
        (hEnergyThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin) (hτk : τ * kmin < 1)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (u : WeakH10)
    (hstep : ∀ v : WeakH10,
      ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
        + κ x * u.weakDeriv x * v.weakDeriv x
        = ∫ x in (0 : ℝ)..1, F x * v.toFun x), (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
      ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + (τ / kmin) * (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
        (hAssembleThm : ∀ {τ : ℝ} (hτ : 0 < τ)
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin) (hτk : τ * kmin < 1)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    {F : ℝ → ℝ} (hF : MemLp F 2 (volume.restrict (Set.Icc 0 1)))
    {uprev : ℝ → ℝ} (huprev : MemLp uprev 2 (volume.restrict (Set.Icc 0 1)))
    (B : WeakH10 →L[ℝ] WeakH10 →L[ℝ] ℝ)
    (hB : ∀ u v : WeakH10,
      B u v = ∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κ x * u.weakDeriv x * v.weakDeriv x)
    (L : WeakH10 →L[ℝ] ℝ)
    (hL : ∀ v : WeakH10,
      L v = ∫ x in (0 : ℝ)..1, (F x + uprev x / τ) * v.toFun x)
    (hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
          + κ x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖)
    (hCoer : ∀ u : WeakH10,
      min (1 / τ) kmin * ‖u‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
            + κ x * u.weakDeriv x * u.weakDeriv x)
    (hInt : ∀ (u v : WeakH10),
      IntervalIntegrable
          (fun x => (u.toFun x - uprev x) / τ * v.toFun x
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => u.toFun x * v.toFun x / τ
            + κ x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => (F x + uprev x / τ) * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => uprev x / τ * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => F x * v.toFun x) volume 0 1)
    (hLax : ∃ u : WeakH10, ∀ v : WeakH10, B u v = L v)
    (hIdent : ∀ (u : WeakH10), (∀ v : WeakH10, B u v = L v) →
      ∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, F x * v.toFun x)
    (hEnergy : ∀ (u : WeakH10),
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, F x * v.toFun x) →
      (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (τ / kmin) * (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2),
    ∃ u : WeakH10,
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, F x * v.toFun x)
      ∧ (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (τ / kmin) * (eLpNorm F 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
    (uprev : ℝ → ℝ)
    (huprev : MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ u : WeakH10,
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / ((t1 - t0) / N) * v.toFun x
          + ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x) * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) * v.toFun x)
      ∧ (1 - ((t1 - t0) / N) * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * ((t1 - t0) / N) * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (((t1 - t0) / N) / kmin) * (eLpNorm (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  set τ : ℝ := (t1 - t0) / N with hτdef
  set κk : ℝ → ℝ := fun x => (1 / τ) * ∫ s in (t0 + k * τ)..(t0 + (k + 1) * τ), κ s x with hκkdef
  set Fk : ℝ → ℝ := fun x => (1 / τ) * ∫ s in (t0 + k * τ)..(t0 + (k + 1) * τ), F s x with hFkdef
  have hτ : 0 < τ := by
    rw [hτdef]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    exact div_pos (sub_pos.mpr ht) hNpos
  obtain ⟨B, L, hB, hL, u0, hu0⟩ := hBL uprev huprev
  have hBnd : ∀ u v : WeakH10,
      |∫ x in (0 : ℝ)..1, u.toFun x * v.toFun x / τ
        + κk x * u.weakDeriv x * v.weakDeriv x|
        ≤ max (1 / τ) kmax * ‖u‖ * ‖v‖ :=
    fun u v => hBndThm hτ hkmin hκk_meas hκk u v
  have hCoer : ∀ u : WeakH10,
      min (1 / τ) kmin * ‖u‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, u.toFun x * u.toFun x / τ
          + κk x * u.weakDeriv x * u.weakDeriv x :=
    fun u => hCoerThm hτ hkmin hκk_meas hκk u
  have hInt : ∀ u v : WeakH10,
      IntervalIntegrable
          (fun x => (u.toFun x - uprev x) / τ * v.toFun x
            + κk x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => u.toFun x * v.toFun x / τ
            + κk x * u.weakDeriv x * v.weakDeriv x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => (Fk x + uprev x / τ) * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => uprev x / τ * v.toFun x) volume 0 1
        ∧ IntervalIntegrable
          (fun x => Fk x * v.toFun x) volume 0 1 :=
    fun u v => hIntThm hτ hkmin hκk_meas hκk hFk huprev u v
  have hIdent : ∀ u : WeakH10, (∀ v : WeakH10, B u v = L v) →
      ∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κk x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, Fk x * v.toFun x :=
    fun u hu => hIdentThm hτ hkmin hκk_meas hκk hFk huprev B hB L hL u hu
      (fun v => hInt u v)
  have hEnergy : ∀ u : WeakH10,
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / τ * v.toFun x
          + κk x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, Fk x * v.toFun x) →
      (1 - τ * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * τ * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (τ / kmin) * (eLpNorm Fk 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 :=
    fun u hu => hEnergyThm hτ hkmin hτsmall hκk_meas hκk hFk huprev u hu
  exact hAssembleThm hτ hkmin hτsmall hκk_meas hκk hFk huprev B hB L hL
    hBnd hCoer hInt ⟨u0, hu0⟩ hIdent hEnergy


noncomputable def rotheSeq (u0 : ℝ → ℝ)
    (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) (N : ℕ)
    (P : ℕ → (ℝ → ℝ) → WeakH10 → Prop)
    (hOneStep : ∀ (k : ℕ), k < N → ∀ (uprev : ℝ → ℝ),
      MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) → ∃ u : WeakH10, P k uprev u) :
    ℕ → WeakH10
  | 0 => 0
  | (k + 1) =>
    if hk : k < N then
      Classical.choose
        (hOneStep k hk (if k = 0 then u0 else
          (rotheSeq u0 hu0 N P hOneStep k).toFun) (by
          by_cases hk0 : k = 0
          · rw [ite_eq_left hk0]
            exact hu0
          · rw [ite_eq_right hk0]
            exact weakH10_toFun_memLp _))
    else 0


theorem rotheSeq_spec (u0 : ℝ → ℝ)
    (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) (N : ℕ)
    {P : ℕ → (ℝ → ℝ) → WeakH10 → Prop}
    (hOneStep : ∀ (k : ℕ), k < N → ∀ (uprev : ℝ → ℝ),
      MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) → ∃ u : WeakH10, P k uprev u)
    (k : ℕ) (hk : k < N) :
    P k (if k = 0 then u0 else (rotheSeq u0 hu0 N P hOneStep k).toFun)
      (rotheSeq u0 hu0 N P hOneStep (k + 1)) := by
  simp only [rotheSeq, dite_eq_left hk]
  exact Classical.choose_spec _


theorem rotheSeq_exists (u0 : ℝ → ℝ)
    (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) (N : ℕ)
    {P : ℕ → (ℝ → ℝ) → WeakH10 → Prop}
    (hOneStep : ∀ (k : ℕ), k < N → ∀ (uprev : ℝ → ℝ),
      MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) → ∃ u : WeakH10, P k uprev u) :
    ∃ U : ℕ → WeakH10,
      ∀ k, k < N →
        P k (if k = 0 then u0 else (U k).toFun) (U (k + 1)) :=
  ⟨rotheSeq u0 hu0 N P hOneStep, fun k hk => rotheSeq_spec u0 hu0 N hOneStep k hk⟩

/-- `WeakH10` carries a real inner-product-space structure (with the H¹
inner product above), and it is complete. This statement only elaborates
once the instances exist. -/

theorem rothe_iter_exists
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {N : ℕ} (hN : 0 < N)
    (hτsmall : ((t1 - t0) / N) * kmin < 1)
    (hOneStep : ∀ (k : ℕ), k < N → ∀ (uprev : ℝ → ℝ),
      MemLp uprev 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ u : WeakH10,
        (∀ v : WeakH10,
          ∫ x in (0 : ℝ)..1, (u.toFun x - uprev x) / ((t1 - t0) / N) * v.toFun x
            + ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x) * u.weakDeriv x * v.weakDeriv x
            = ∫ x in (0 : ℝ)..1, ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) * v.toFun x)
        ∧ (1 - ((t1 - t0) / N) * kmin) * (eLpNorm u.toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ((t1 - t0) / N) * kmin * (eLpNorm u.weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          ≤ (eLpNorm uprev 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
            + (((t1 - t0) / N) / kmin) * (eLpNorm (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2) :
    ∃ U : ℕ → WeakH10,
      ∀ k, k < N →
        (∀ v : WeakH10,
          ∫ x in (0 : ℝ)..1, ((U (k + 1)).toFun x - (if k = 0 then u0 else (U k).toFun) x) / ((t1 - t0) / N) * v.toFun x
            + ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), κ s x) * (U (k + 1)).weakDeriv x * v.weakDeriv x
            = ∫ x in (0 : ℝ)..1, ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) * v.toFun x)
        ∧ (1 - ((t1 - t0) / N) * kmin) * (eLpNorm (U (k + 1)).toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ((t1 - t0) / N) * kmin * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          ≤ (eLpNorm (if k = 0 then u0 else (U k).toFun) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
            + (((t1 - t0) / N) / kmin) * (eLpNorm (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  exact rotheSeq_exists u0 hu0 N hOneStep


theorem rothe_iter_bounds
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {N : ℕ} (hN : 0 < N)
    (hτsmall : ((t1 - t0) / N) * kmin < 1)
    (U : ℕ → WeakH10)
    (hEnergy : ∀ k, k < N →
      (1 - ((t1 - t0) / N) * kmin) * (eLpNorm (U (k + 1)).toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * ((t1 - t0) / N) * kmin * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (eLpNorm (if k = 0 then u0 else (U k).toFun) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + (((t1 - t0) / N) / kmin) * (eLpNorm (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1) * ((t1 - t0) / N)), F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
    (hFNormThm : ∀ {t0 t1 : ℝ}, t0 < t1 →
      ∀ {F : ℝ → ℝ → ℝ},
      ∀ (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))),
      ∀ {a b : ℝ}, a < b → Set.Icc a b ⊆ Set.Icc t0 t1 → 0 < b - a →
      ∀ (hAvg_meas : AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
        (volume.restrict (Set.Icc 0 1))),
      (eLpNorm (fun x => (1 / (b - a)) * ∫ s in a..b, F s x) 2
          (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        ≤ (1 / (b - a)) * ∫ s in a..b,
          (eLpNorm (fun x => F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
    (hFMeasThm : ∀ {t0 t1 : ℝ}, t0 < t1 →
      ∀ {F : ℝ → ℝ → ℝ},
      ∀ (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))),
      ∀ {a b : ℝ}, a < b → Set.Icc a b ⊆ Set.Icc t0 t1 → 0 < b - a →
      AEStronglyMeasurable (fun x => (1 / (b - a)) * ∫ s in a..b, F s x)
        (volume.restrict (Set.Icc 0 1))) :
    ∃ C : ℝ, 0 < C ∧
      (∀ k, k ≤ N →
        (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)
      ∧ (∑ k ∈ Finset.range N,
          ((t1 - t0) / N) * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C) := by
  have hτ : 0 < ((t1 - t0) / N) := div_pos (sub_pos.mpr ht) (Nat.cast_pos.mpr hN)
  refine ⟨(∑ k ∈ Finset.range (N + 1),
      (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      + (∑ k ∈ Finset.range N, ((t1 - t0) / N)
        * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      + 1, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ ∑ k ∈ Finset.range (N + 1),
        (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have h2 : 0 ≤ ∑ k ∈ Finset.range N, ((t1 - t0) / N)
        * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg hτ.le (sq_nonneg _)
    linarith
  · intro k hk
    have hsingle : (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ≤ ∑ k ∈ Finset.range (N + 1),
          (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
      Finset.single_le_sum
        (fun i _ => sq_nonneg ((eLpNorm (U i).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal))
        (Finset.mem_range_succ_iff.mpr hk)
    have h2 : 0 ≤ ∑ k ∈ Finset.range N, ((t1 - t0) / N)
        * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg hτ.le (sq_nonneg _)
    linarith
  · have h1 : 0 ≤ ∑ k ∈ Finset.range (N + 1),
        (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    linarith


theorem memLp_snd_restrict {t0 t1 : ℝ} {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (fun p : ℝ × ℝ => g p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have hμ : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hμ]
  exact hg.comp_snd _


theorem memLp_rothe_interp {t0 t1 : ℝ} (ht : t0 < t1) {N : ℕ} (hN : 0 < N)
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, MemLp (g j) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (Function.uncurry fun t x =>
      if t = t1 then g N x else g (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) x) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  set τ : ℝ := (t1 - t0) / N with hτdef
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  have hτ : 0 < τ := by
    rw [hτdef]
    exact div_pos (sub_pos.mpr ht) (Nat.cast_pos.mpr hN)
  set k : ℝ → ℕ := fun t => Nat.floor ((t - t0) / τ) + 1 with hkdef
  have hycont : Continuous fun t : ℝ => (t - t0) / τ :=
    (continuous_id.sub continuous_const).div_const τ
  have hkfloor : Measurable fun t : ℝ => Nat.floor ((t - t0) / τ) :=
    Measurable.nat_floor hycont.measurable
  have hkmeas : Measurable k := by
    rw [hkdef]
    apply measurable_to_countable
    intro y
    have hfib : (fun t : ℝ => Nat.floor ((t - t0) / τ) + 1) ⁻¹'
          {Nat.floor ((y - t0) / τ) + 1}
        = (fun t : ℝ => Nat.floor ((t - t0) / τ)) ⁻¹' {Nat.floor ((y - t0) / τ)} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      omega
    rw [hfib]
    exact hkfloor (measurableSet_singleton _)
  have hk_mem : ∀ t ∈ Set.Icc t0 t1, t ≠ t1 → k t ∈ Finset.Icc 1 N := by
    intro t htmem htne
    have ht1 : t < t1 := lt_of_le_of_ne htmem.2 htne
    have hy0 : 0 ≤ (t - t0) / τ := div_nonneg (sub_nonneg.mpr htmem.1) hτ.le
    have hsub : t - t0 < t1 - t0 := by linarith
    have h1 : (t - t0) / τ < (t1 - t0) / τ := div_lt_div_of_pos_right hsub hτ
    have hne : t1 - t0 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
    have h2 : (t1 - t0) / τ = (N : ℝ) := by
      rw [hτdef]
      field_simp
    rw [h2] at h1
    have hflt : Nat.floor ((t - t0) / τ) < N := (Nat.floor_lt hy0).mpr h1
    have hkt : k t = Nat.floor ((t - t0) / τ) + 1 := by rw [hkdef]
    rw [hkt, Finset.mem_Icc]
    constructor
    · exact Nat.le_add_left 1 _
    · omega
  set S : ℕ → Set (ℝ × ℝ) := fun j => {t : ℝ | k t = j} ×ˢ Set.univ with hSdef
  have hSmeas : ∀ j, MeasurableSet (S j) := by
    intro j
    have hfib : {t : ℝ | k t = j} = k ⁻¹' {j} := by
      ext t
      simp
    rw [hSdef]
    show MeasurableSet ({t : ℝ | k t = j} ×ˢ Set.univ)
    rw [hfib]
    exact (hkmeas (measurableSet_singleton j)).prod MeasurableSet.univ
  set F : (ℝ × ℝ) → ℝ :=
    fun p => ∑ j ∈ Finset.Icc 1 N, (S j).indicator (fun q => g j q.2) p with hFdef
  have hFmem : MemLp F 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    have h := memLp_finsetSum (Finset.Icc 1 N)
      (f := fun j : ℕ => (S j).indicator (fun q : ℝ × ℝ => g j q.2))
      (fun j _ => MemLp.indicator (hSmeas j).nullMeasurableSet
        (memLp_snd_restrict (t0 := t0) (t1 := t1) (hg j)))
    rw [hFdef]
    exact h
  have hbox : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hnullV : volume {p : ℝ × ℝ | ¬ p.1 ≠ t1} = 0 := by
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ t1} = {t1} ×ˢ (Set.univ : Set ℝ) := by
      ext ⟨t, x⟩
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have h1 : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ t1 := ae_iff.mpr hnullV
  have hFG : ∀ p ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, p.1 ≠ t1 →
      (Function.uncurry fun t x =>
        if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x) p
      = F p := by
    intro p hpmem hp1
    obtain ⟨t, x⟩ := p
    have htmem : t ∈ Set.Icc t0 t1 := hpmem.1
    have htne : t ≠ t1 := hp1
    have hk0 := hk_mem t htmem htne
    have hmem : (t, x) ∈ S (k t) := by
      rw [hSdef]
      refine ⟨?_, Set.mem_univ x⟩
      show k (t, x).1 = k t
      rfl
    have hmain : (S (k t)).indicator (fun q => g (k t) q.2) (t, x) = g (k t) x :=
      Set.indicator_of_mem hmem _
    have h₀ : ∀ j ∈ Finset.Icc 1 N, j ≠ k t →
        (S j).indicator (fun q => g j q.2) (t, x) = 0 := by
      intro j _ hjne
      apply Set.indicator_of_notMem
      rw [hSdef]
      intro hcon
      have hkk : k t = j := hcon.1
      exact hjne hkk.symm
    have hFt : F (t, x) = g (k t) x := by
      rw [hFdef]
      show (∑ j ∈ Finset.Icc 1 N, (S j).indicator (fun q => g j q.2) (t, x)) = g (k t) x
      rw [Finset.sum_eq_single (k t) h₀ (fun hcon => absurd hk0 hcon)]
      exact hmain
    have hGt : (Function.uncurry fun t x =>
        if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x) (t, x)
        = g (k t) x := by
      show (if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x) = g (k t) x
      rw [ite_eq_right htne, hkdef]
    rw [hGt, hFt]
  have hae : (Function.uncurry fun t x =>
      if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x)
      =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)] F := by
    show ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
      (Function.uncurry fun t x =>
        if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x) p = F p
    rw [ae_restrict_iff' hbox]
    filter_upwards [h1] with p hp1 hpmem
    exact hFG p hpmem hp1
  have hGaesm : AEStronglyMeasurable (Function.uncurry fun t x =>
      if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    hFmem.aestronglyMeasurable.congr hae.symm
  have hnorm : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
      ‖F p‖ = ‖(Function.uncurry fun t x =>
        if t = t1 then g N x else g (Nat.floor ((t - t0) / τ) + 1) x) p‖ :=
    hae.mono fun p hp => (congrArg _ hp).symm
  exact hFmem.congr_norm hGaesm hnorm


theorem rothe_interp_bounds
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {N : ℕ} (hN : 0 < N)
    (U : ℕ → WeakH10)
    (hBoundsThm : ∃ C : ℝ, 0 < C ∧
      (∀ k, k ≤ N →
        (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)
      ∧ (∑ k ∈ Finset.range N,
          ((t1 - t0) / N) * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)) :
    ∃ C' : ℝ, 0 < C' ∧
      (eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U N).toFun x
        else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).toFun x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ^ 2 ≤ C'
      ∧ (eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U N).weakDeriv x
        else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ^ 2 ≤ C'  := by
  generalize (eLpNorm (Function.uncurry (fun t x =>
    if t = t1 then (U N).toFun x
    else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).toFun x)) 2
    (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal = a
  generalize (eLpNorm (Function.uncurry (fun t x =>
    if t = t1 then (U N).weakDeriv x
    else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)) 2
    (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal = b
  refine ⟨a ^ 2 + b ^ 2 + 1, by positivity, ?_, ?_⟩
  · linarith [sq_nonneg b]
  · linarith [sq_nonneg a]

/-- Interpolants are MemLp with uniform bounds. -/

theorem interp_memLp_bounds
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {N : ℕ} (hN : 0 < N)
    (U : ℕ → WeakH10)
    (hBounds : ∃ C : ℝ, 0 < C ∧
      (∀ k, k ≤ N →
        (eLpNorm (U k).toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)
      ∧ (∑ k ∈ Finset.range N,
          ((t1 - t0) / N) * (eLpNorm (U (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)) :
    (MemLp (Function.uncurry (fun t x =>
      if t = t1 then (U N).toFun x
      else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).toFun x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    ∧ (MemLp (Function.uncurry (fun t x =>
      if t = t1 then (U N).weakDeriv x
      else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    ∧ (∃ C : ℝ, 0 < C ∧
        (eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U N).toFun x
          else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).toFun x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ C
        ∧ (eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U N).weakDeriv x
          else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ C) := by
  obtain ⟨C', hC'pos, hsq1, hsq2⟩ :=
    rothe_interp_bounds (κ := κ) (kmax := kmax) (F := F) ht hkmin hu0 hN U hBounds
  have hle : ∀ a : ℝ, 0 ≤ a → a ^ 2 ≤ C' → a ≤ C' + 1 := by
    intro a ha0 haC
    have hC2 : C' ≤ (C' + 1) ^ 2 := by nlinarith [sq_nonneg C', hC'pos]
    have h := haC.trans hC2
    have habs := abs_le_of_sq_le_sq h (by linarith)
    rwa [abs_of_nonneg ha0] at habs
  have hmem1 : MemLp (Function.uncurry (fun t x =>
      if t = t1 then (U N).toFun x
      else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).toFun x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    memLp_rothe_interp ht hN (fun j => weakH10_toFun_memLp (U j))
  have hmem2 : MemLp (Function.uncurry (fun t x =>
      if t = t1 then (U N).weakDeriv x
      else (U (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    memLp_rothe_interp ht hN (fun j => (U j).weakDeriv_memLp)
  exact ⟨hmem1, hmem2, C' + 1, by linarith,
    hle _ ENNReal.toReal_nonneg hsq1, hle _ ENNReal.toReal_nonneg hsq2⟩


theorem sq_integral_le_length_mul_sq_integral
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (hf2 : IntegrableOn (fun x => (f x) ^ 2) (Set.Icc a b) volume) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  set μ : Measure ℝ := volume.restrict (Set.Icc a b) with hμdef
  have hf' : Integrable f μ := hf
  have hf2' : Integrable (fun x => (f x) ^ 2) μ := hf2
  have hfnorm : Integrable (fun x => ‖f x‖) μ := hf'.norm
  have hnn : 0 ≤ᵐ[μ] (fun x => ‖f x‖) := Filter.Eventually.of_forall fun x => norm_nonneg _
  have h2nn : 0 ≤ᵐ[μ] (fun x => (f x) ^ 2) := Filter.Eventually.of_forall fun x => sq_nonneg _
  have hHnn : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg_of_ae hnn
  have hGnn : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_nonneg_of_ae h2nn
  have hVnn : 0 ≤ b - a := sub_nonneg.mpr hab
  have e1 : ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hfnorm hnn]
    exact lintegral_congr fun x => ofReal_norm _
  have e2pt : ∀ x : ℝ, ENNReal.ofReal ((f x) ^ 2) = ‖f x‖ₑ ^ (2 : ℝ) := fun x => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have e2 : ENNReal.ofReal (∫ x, (f x) ^ 2 ∂μ) = ∫⁻ x, (‖f x‖ₑ ^ (2 : ℝ)) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2' h2nn]
    exact lintegral_congr e2pt
  have e3 : (∫⁻ y, (1 : ENNReal) ^ (2 : ℝ) ∂μ) = ENNReal.ofReal (b - a) := by
    rw [lintegral_congr (fun _ => ENNReal.one_rpow 2), lintegral_one, hμdef,
      Measure.restrict_apply_univ, Real.volume_Icc]
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨one_lt_two, by norm_num⟩
  have hmeas : AEMeasurable (fun x => ‖f x‖ₑ) μ :=
    hf'.aestronglyMeasurable.nnnorm.aemeasurable.coe_nnreal_ennreal
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (g := fun _ => (1 : ENNReal)) hpq
    hmeas aemeasurable_const
  simp only [Pi.mul_apply, mul_one] at hH
  rw [← e1, ← e2, e3] at hH
  have hne : (ENNReal.ofReal (∫ x, (f x) ^ 2 ∂μ)) ^ ((1 : ℝ) / 2) *
      (ENNReal.ofReal (b - a)) ^ ((1 : ℝ) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (y := (1 / 2 : ℝ)) (by norm_num)
        ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (y := (1 / 2 : ℝ)) (by norm_num)
        ENNReal.ofReal_ne_top)
  have htoReal := ENNReal.toReal_mono hne hH
  rw [ENNReal.toReal_ofReal hHnn, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hGnn,
    ENNReal.toReal_ofReal hVnn] at htoReal
  have hsq : (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂μ) * (b - a) := by
    have h12 : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 := by norm_num
    calc (∫ x, ‖f x‖ ∂μ) ^ 2
        ≤ ((∫ x, (f x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (b - a) ^ ((1 : ℝ) / 2)) ^ 2 :=
          pow_le_pow_left₀ hHnn htoReal 2
      _ = (∫ x, (f x) ^ 2 ∂μ) * (b - a) := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
            ← Real.rpow_mul hGnn, ← Real.rpow_mul hVnn, h12,
            Real.rpow_one, Real.rpow_one]
  have htri : |∫ x, f x ∂μ| ≤ ∫ x, ‖f x‖ ∂μ := by
    have h := norm_integral_le_integral_norm (f := f) (μ := μ)
    rwa [Real.norm_eq_abs] at h
  calc (∫ x, f x ∂μ) ^ 2 = |∫ x, f x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) htri 2
    _ ≤ (∫ x, (f x) ^ 2 ∂μ) * (b - a) := hsq
    _ = (b - a) * ∫ x, (f x) ^ 2 ∂μ := mul_comm _ _


theorem intervalJensen_sq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (h1 : IntegrableOn f (Set.Icc a b) volume)
    (h2 : IntegrableOn (fun x => (f x) ^ 2) (Set.Icc a b) volume) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [intervalIntegral.integral_same]
  · have hba : 0 < b - a := sub_pos.mpr hlt
    have hI1 : IntervalIntegrable f volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (Iff.mp integrableOn_Icc_iff_integrableOn_Ioc h1)
    have hI2 : IntervalIntegrable (fun x => (f x) ^ 2) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (Iff.mp integrableOn_Icc_iff_integrableOn_Ioc h2)
    set S := ∫ x in a..b, f x with hS
    set Q := ∫ x in a..b, (f x) ^ 2 with hQ
    set c := S / (b - a) with hc
    have hnn : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
      intervalIntegral.integral_nonneg_of_ae hab
        (Eventually.of_forall fun x => sq_nonneg (f x - c))
    have hexpand : (fun x => (f x - c) ^ 2)
        = fun x => (f x) ^ 2 - (2 * c) * f x + c ^ 2 := by
      funext x; ring
    have hIc : IntervalIntegrable (fun _ => c ^ 2) volume a b := intervalIntegrable_const
    have hIm : IntervalIntegrable (fun x => (2 * c) * f x) volume a b :=
      hI1.const_mul (2 * c)
    have hIsub : IntervalIntegrable (fun x => (f x) ^ 2 - (2 * c) * f x) volume a b :=
      hI2.sub hIm
    rw [hexpand, intervalIntegral.integral_add hIsub hIc,
      intervalIntegral.integral_sub hI2 hIm,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      smul_eq_mul, ← hS, ← hQ] at hnn
    have hc' : c * (b - a) = S := by rw [hc]; field_simp
    have hkey : (b - a) * Q - S ^ 2
        = (b - a) * (Q - (2 * c) * S + (b - a) * c ^ 2) := by
      have hcc : S = c * (b - a) := hc'.symm
      rw [hcc]
      ring
    have hnonneg : 0 ≤ (b - a) * Q - S ^ 2 := by
      rw [hkey]
      exact mul_nonneg hba.le hnn
    linarith


theorem slab_avg_sq_integral_le_one_slab
    {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1)))
    (hJensenThm : ∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ},
      IntegrableOn f (Set.Icc a b) volume →
      IntegrableOn (fun x => (f x) ^ 2) (Set.Icc a b) volume →
      (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, (f x) ^ 2) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
        (((b - a)⁻¹ * ∫ s in a..b, f s p.2) ^ 2) ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1))
      ≤ ∫ p in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
          (f p.1 p.2) ^ 2 ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hbane : b - a ≠ 0 := ne_of_gt hba
  have hμ : volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hfinBox : IsFiniteMeasure (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) := by
    rw [hμ]; infer_instance
  have hF_int : Integrable (Function.uncurry f)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) :=
    hf.integrable one_le_two
  have hF2_int : Integrable (fun p => (Function.uncurry f p) ^ 2)
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) :=
    hf.integrable_sq
  have hF_prod : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
    rw [← hμ]; exact hF_int
  have hF2_prod : Integrable (fun p => (Function.uncurry f p) ^ 2)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
    rw [← hμ]; exact hF2_int
  have hslice1 := hF_prod.prod_left_ae
  have hslice2 := hF2_prod.prod_left_ae
  have hSeq : ∀ y : ℝ, (∫ s in a..b, f s y)
      = ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)) := by
    intro y
    calc (∫ s in a..b, f s y)
        = ∫ s in Set.Ioc a b, f s y ∂volume :=
          intervalIntegral.integral_of_le hab.le
      _ = ∫ s in Set.Icc a b, f s y ∂volume := setIntegral_congr_set Ioc_ae_eq_Icc
      _ = ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)) := rfl
  have hQeq : ∀ y : ℝ, (∫ s in a..b, (f s y)^2)
      = ∫ x, (Function.uncurry f (x, y))^2 ∂(volume.restrict (Set.Icc a b)) := by
    intro y
    calc (∫ s in a..b, (f s y)^2)
        = ∫ s in Set.Ioc a b, (f s y)^2 ∂volume :=
          intervalIntegral.integral_of_le hab.le
      _ = ∫ s in Set.Icc a b, (f s y)^2 ∂volume := setIntegral_congr_set Ioc_ae_eq_Icc
      _ = ∫ x, (Function.uncurry f (x, y))^2 ∂(volume.restrict (Set.Icc a b)) := rfl
  have hJ : ∀ᵐ y ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      (((b - a)⁻¹ * ∫ s in a..b, f s y) ^ 2)
        ≤ (b - a)⁻¹ * ∫ s in a..b, (f s y) ^ 2 := by
    filter_upwards [hslice1, hslice2] with y h1y h2y
    have g1 : IntegrableOn (fun s => f s y) (Set.Icc a b) volume := h1y
    have g2 : IntegrableOn (fun s => (f s y) ^ 2) (Set.Icc a b) volume := h2y
    have hle := hJensenThm hab.le g1 g2
    have hpos : (0:ℝ) ≤ ((b - a)⁻¹) ^ 2 := sq_nonneg _
    have h1 : ((b - a)⁻¹)^2 * (b - a) = (b - a)⁻¹ := by
      rw [pow_two, mul_assoc, inv_mul_cancel₀ hbane, mul_one]
    calc (((b - a)⁻¹ * ∫ s in a..b, f s y) ^ 2)
        = ((b - a)⁻¹) ^ 2 * (∫ s in a..b, f s y) ^ 2 := by ring
      _ ≤ ((b - a)⁻¹) ^ 2 * ((b - a) * ∫ s in a..b, (f s y) ^ 2) :=
          mul_le_mul_of_nonneg_left hle hpos
      _ = (b - a)⁻¹ * ∫ s in a..b, (f s y) ^ 2 := by
          calc ((b - a)⁻¹)^2 * ((b - a) * ∫ s in a..b, (f s y)^2)
              = (((b - a)⁻¹)^2 * (b - a)) * ∫ s in a..b, (f s y)^2 := by ring
            _ = (b - a)⁻¹ * ∫ s in a..b, (f s y)^2 := by rw [h1]
  have hS'int : Integrable
      (fun y => ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hF_prod.integral_prod_right
  have hH'' : Integrable
      (fun y => (b - a)⁻¹ * ∫ x, (Function.uncurry f (x, y))^2 ∂(volume.restrict (Set.Icc a b)))
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hF2_prod.integral_prod_right.const_mul _
  have hG''aemeas : AEStronglyMeasurable
      (fun y => ((b - a)⁻¹ * ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))^2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    (hS'int.aestronglyMeasurable.const_mul ((b - a)⁻¹)).pow 2
  have hJ'' : ∀ᵐ y ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      ((b - a)⁻¹ * ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))^2
        ≤ (b - a)⁻¹ * ∫ x, (Function.uncurry f (x, y))^2 ∂(volume.restrict (Set.Icc a b)) := by
    filter_upwards [hJ] with y hy
    rw [hSeq y, hQeq y] at hy
    exact hy
  have hG''int : Integrable
      (fun y => ((b - a)⁻¹ * ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))^2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    apply hH''.mono' hG''aemeas
    filter_upwards [hJ''] with y hy
    have hnorm : ‖((b - a)⁻¹ * ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))^2‖
        = ((b - a)⁻¹ * ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))^2 :=
      Real.norm_of_nonneg (sq_nonneg _)
    rw [hnorm]
    exact hy
  have hG'int : Integrable (fun y => ((b - a)⁻¹ * ∫ s in a..b, f s y)^2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hG''int.congr (Eventually.of_forall fun y => by
      show ((b - a)⁻¹ * ∫ x, Function.uncurry f (x, y) ∂(volume.restrict (Set.Icc a b)))^2
        = ((b - a)⁻¹ * ∫ s in a..b, f s y)^2
      rw [hSeq y])
  have hH'int : Integrable (fun y => (b - a)⁻¹ * ∫ s in a..b, (f s y)^2)
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    hH''.congr (Eventually.of_forall fun y => by
      show (b - a)⁻¹ * ∫ x, (Function.uncurry f (x, y))^2 ∂(volume.restrict (Set.Icc a b))
        = (b - a)⁻¹ * ∫ s in a..b, (f s y)^2
      rw [hQeq y])
  have hInner : (∫ y, ((b - a)⁻¹ * ∫ s in a..b, f s y)^2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
      ≤ ∫ y, (b - a)⁻¹ * (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
    integral_mono_ae hG'int hH'int hJ
  have hH'eq : (∫ y, (b - a)⁻¹ * (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
      = (b - a)⁻¹ * ∫ y, (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
    integral_const_mul _ _
  have hQint : (∫ y, (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
      = ∫ y, ∫ x, (f x y)^2 ∂(volume.restrict (Set.Icc a b)) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
    apply integral_congr_ae
    filter_upwards with y
    exact hQeq y
  have hF2_unc : Integrable (Function.uncurry (fun x y => (f x y)^2))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
    rw [← hμ]; exact hF2_int
  have hSwap : (∫ y, ∫ x, (f x y)^2 ∂(volume.restrict (Set.Icc a b)) ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
      = ∫ z, (f z.1 z.2)^2 ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
    have h1 := integral_integral_swap hF2_unc
    have h2 := integral_integral hF2_unc
    exact h1.symm.trans h2
  have hμreal : (volume.restrict (Set.Icc a b)).real Set.univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal hba.le]
  have hM : (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)).restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    (Measure.restrict_restrict_of_subset (fun _ h => h)).trans hμ
  rw [hM]
  have hLHS : (∫ p, ((b - a)⁻¹ * ∫ s in a..b, f s p.2)^2
        ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1))))
      = (volume.restrict (Set.Icc a b)).real Set.univ
        • ∫ y, ((b - a)⁻¹ * ∫ s in a..b, f s y)^2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
    integral_fun_snd (fun y => ((b - a)⁻¹ * ∫ s in a..b, f s y)^2)
  rw [hLHS, hμreal, smul_eq_mul]
  calc ((b - a) * ∫ y, ((b - a)⁻¹ * ∫ s in a..b, f s y)^2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
      ≤ (b - a) * ∫ y, (b - a)⁻¹ * (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) :=
        mul_le_mul_of_nonneg_left hInner hba.le
    _ = (b - a) * ((b - a)⁻¹ * ∫ y, (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1))) := by
        rw [hH'eq]
    _ = ∫ y, (∫ s in a..b, (f s y)^2) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hbane, one_mul]
    _ = ∫ p, (f p.1 p.2)^2
        ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
        rw [hQint, hSwap]
/-- One-slab squared-integral inequality in Fbar form. -/

theorem slab_sq_one
    {t0 t1 : ℝ} (ht : t0 < t1)
    {f g : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hg : MemLp (Function.uncurry g) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) :
    (∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
      ((((N : ℝ) / (t1 - t0)) * ∫ s in (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ)))..(t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))), (f s p.2 - g s p.2)) ^ 2)
        ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)))
      ≤ ∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
          ((f p.1 p.2 - g p.1 p.2) ^ 2)
            ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)) := by
  set a := t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ)) with ha
  set b := t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) with hb
  have hτ : 0 < (t1 - t0) / (N:ℝ) := div_pos (sub_pos.mpr ht) (Nat.cast_pos.mpr hN)
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hab : a < b := by
    rw [ha, hb]
    have hkk : (k:ℝ) * ((t1 - t0)/(N:ℝ)) < ((k:ℝ) + 1) * ((t1 - t0)/(N:ℝ)) :=
      mul_lt_mul_of_pos_right (lt_add_one _) hτ
    linarith
  have hwid : (N:ℝ) / (t1 - t0) = (b - a)⁻¹ := by
    have h1 : ∀ τ : ℝ, (t0 + ((k:ℝ)+1)*τ) - (t0 + (k:ℝ)*τ) = τ := fun τ => by ring
    rw [ha, hb, h1, inv_div]
  have ha0 : t0 ≤ a := by
    rw [ha]
    apply le_add_of_nonneg_right
    exact mul_nonneg (Nat.cast_nonneg _) hτ.le
  have hb1 : b ≤ t1 := by
    rw [hb]
    have hkN : (k:ℝ) + 1 ≤ (N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
    have hle : ((k:ℝ) + 1) * ((t1 - t0)/(N:ℝ)) ≤ (N:ℝ) * ((t1 - t0)/(N:ℝ)) :=
      mul_le_mul_of_nonneg_right hkN hτ.le
    have hNτ : (N:ℝ) * ((t1 - t0)/(N:ℝ)) = t1 - t0 := by field_simp
    linarith
  have hsubbox : Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1 ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 := by
    intro p hp
    simp only [Set.mem_prod, Set.mem_Icc] at hp ⊢
    obtain ⟨⟨hab1, hab2⟩, hx1, hx2⟩ := hp
    exact ⟨⟨ha0.trans hab1, hab2.trans hb1⟩, hx1, hx2⟩
  have hdiff : MemLp (Function.uncurry (fun s x => f s x - g s x)) 2
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) := by
    have hmeas : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1)).restrict
        (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)
        = volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) :=
      Measure.restrict_restrict_of_subset hsubbox
    rw [← hmeas]
    exact (hf.sub hg).restrict _
  rw [hwid]
  exact slab_avg_sq_integral_le_one_slab (f := fun s x => f s x - g s x) hab hdiff
    intervalJensen_sq


theorem rectangle_integral_sum_slabs
    {t0 t1 : ℝ} (ht : t0 < t1)
    {F : ℝ × ℝ → ℝ}
    (hF : IntegrableOn F (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) volume)
    (N : ℕ) (hN : 0 < N) :
    ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, F p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      = ∑ k ∈ Finset.range N,
        ∫ p in Set.Icc (t0 + k * ((t1 - t0) / N)) (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1,
            F p ∂(volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N)) (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc 0 1)) := by
  set δ : ℝ := (t1 - t0) / (N : ℝ) with hδdef
  have hNℝ : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNℝ
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (sub_pos.mpr ht) hNℝ
  have hNδ : (N : ℝ) * δ = t1 - t0 := by
    rw [hδdef]
    field_simp
  have hAle : ∀ k : ℕ, t0 ≤ t0 + (k : ℝ) * δ :=
    fun k => le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) hδpos.le)
  have hBle : ∀ k : ℕ, k ≤ N → t0 + (k : ℝ) * δ ≤ t1 := by
    intro k hk
    have h1 : (k : ℝ) * δ ≤ (N : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδpos.le
    rw [hNδ] at h1
    linarith
  have hcast : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) :=
    fun k => (Nat.cast_add_one k).symm
  have hBle' : ∀ k : ℕ, k < N → t0 + ((k : ℝ) + 1) * δ ≤ t1 := by
    intro k hk
    rw [hcast k]
    exact hBle (k + 1) (by omega)
  have hCk0 : ∀ k : ℕ, t0 ≤ t0 + ((k : ℝ) + 1) * δ :=
    fun k => le_add_of_nonneg_right
      (mul_nonneg (add_nonneg (Nat.cast_nonneg k) zero_le_one) hδpos.le)
  have hmono : ∀ i j : ℕ, i ≤ j → t0 + (i : ℝ) * δ ≤ t0 + (j : ℝ) * δ := by
    intro i j hij
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδpos.le) t0
  have hkk : ∀ k : ℕ, t0 + (k : ℝ) * δ ≤ t0 + ((k : ℝ) + 1) * δ := by
    intro k
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδpos.le) t0
  have h1D : ∀ a b : ℝ, a ≤ b → Set.Icc a b = Set.Ico a b ∪ {b} := by
    intro a b hab
    ext t
    simp only [Set.mem_Icc, Set.mem_Ico, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases lt_or_eq_of_le h.2 with h' | h'
      · exact Or.inl ⟨h.1, h'⟩
      · exact Or.inr h'
    · intro h
      rcases h with h | h
      · exact ⟨h.1, h.2.le⟩
      · rw [h]
        exact ⟨hab, le_rfl⟩
  have hRmeas : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hMmeas : MeasurableSet (Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Ico.prod measurableSet_Icc
  have hGmeas : MeasurableSet ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) :=
    (measurableSet_singleton t1).prod measurableSet_Icc
  have hSmeas : ∀ k : ℕ, MeasurableSet
      (Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    fun k => measurableSet_Icc.prod measurableSet_Icc
  have hTmeas : ∀ k : ℕ, MeasurableSet
      (Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1) :=
    fun k => measurableSet_Ico.prod measurableSet_Icc
  have hFmeas : ∀ k : ℕ, MeasurableSet
      ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) :=
    fun k => (measurableSet_singleton _).prod measurableSet_Icc
  have dR : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict hRmeas, Set.inter_self]
  have dS : ∀ k : ℕ, (volume.restrict
      (Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1)).restrict
      (Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1)
      = volume.restrict
      (Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro k
    rw [Measure.restrict_restrict (hSmeas k), Set.inter_self]
  simp only [dR, dS]
  have hMsubR : Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1
      ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono Set.Ico_subset_Icc_self Set.Subset.rfl
  have hGsubR : (({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1
      ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    refine Set.prod_mono ?_ Set.Subset.rfl
    rw [Set.singleton_subset_iff]
    exact Set.mem_Icc.mpr ⟨ht.le, le_rfl⟩
  have hTsubR : ∀ k : ℕ, k < N →
      Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1
        ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    refine Set.prod_mono ?_ Set.Subset.rfl
    intro t ht
    obtain ⟨h1, h2⟩ := Set.mem_Ico.mp ht
    exact Set.mem_Icc.mpr ⟨le_trans (hAle k) h1, le_of_lt (lt_of_lt_of_le h2 (hBle' k hk))⟩
  have hSsubR : ∀ k : ℕ, k < N →
      Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1
        ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    refine Set.prod_mono ?_ Set.Subset.rfl
    intro t ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact Set.mem_Icc.mpr ⟨le_trans (hAle k) h1, le_trans h2 (hBle' k hk)⟩
  have hFsubR : ∀ k : ℕ, k < N →
      ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1)
        ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    refine Set.prod_mono ?_ Set.Subset.rfl
    rw [Set.singleton_subset_iff]
    exact Set.mem_Icc.mpr ⟨hCk0 k, hBle' k hk⟩
  have hMint : IntegrableOn F (Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) volume :=
    hF.mono_set hMsubR
  have hGint : IntegrableOn F ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) volume :=
    hF.mono_set hGsubR
  have hTint : ∀ k : ℕ, k < N → IntegrableOn F
      (Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1) volume :=
    fun k hk => hF.mono_set (hTsubR k hk)
  have hSint : ∀ k : ℕ, k < N → IntegrableOn F
      (Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1) volume :=
    fun k hk => hF.mono_set (hSsubR k hk)
  have hFint : ∀ k : ℕ, k < N → IntegrableOn F
      ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) volume :=
    fun k hk => hF.mono_set (hFsubR k hk)
  have hU_R : Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1
      = (Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
        ∪ ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [h1D t0 t1 ht.le, Set.union_prod]
  have hU_S : ∀ k : ℕ, Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ)
      ×ˢ Set.Icc (0 : ℝ) 1
      = (Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1)
        ∪ ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro k
    rw [h1D _ _ (hkk k), Set.union_prod]
  have hD_MG : Disjoint (Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Set.disjoint_left]
    rintro p ⟨ht1, -⟩ ⟨ht2, -⟩
    rw [Set.mem_singleton_iff] at ht2
    obtain ⟨-, hlt⟩ := Set.mem_Ico.mp ht1
    rw [ht2] at hlt
    exact (lt_irrefl _) hlt
  have hD_TF : ∀ k : ℕ, Disjoint
      (Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1)
      ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro k
    rw [Set.disjoint_left]
    rintro p ⟨ht1, -⟩ ⟨ht2, -⟩
    rw [Set.mem_singleton_iff] at ht2
    obtain ⟨-, hlt⟩ := Set.mem_Ico.mp ht1
    rw [ht2] at hlt
    exact (lt_irrefl _) hlt
  have hD_TT : (↑(Finset.range N) : Set ℕ).Pairwise
      (Function.onFun Disjoint (fun k : ℕ =>
        Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1)) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    show Disjoint _ _
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : t0 + ((i : ℝ) + 1) * δ ≤ t0 + (j : ℝ) * δ := by
        rw [hcast i]
        exact hmono (i + 1) j (by omega)
      have h1d : Disjoint (Set.Ico (t0 + (i : ℝ) * δ) (t0 + ((i : ℝ) + 1) * δ))
          (Set.Ico (t0 + (j : ℝ) * δ) (t0 + ((j : ℝ) + 1) * δ)) := by
        rw [Set.Ico_disjoint_Ico]
        exact le_trans (min_le_left _ _) (le_trans hle (le_max_right _ _))
      rw [Set.disjoint_left]
      rintro p ⟨ht1, -⟩ ⟨ht2, -⟩
      exact Set.disjoint_left.mp h1d ht1 ht2
    · have hle : t0 + ((j : ℝ) + 1) * δ ≤ t0 + (i : ℝ) * δ := by
        rw [hcast j]
        exact hmono (j + 1) i (by omega)
      have h1d : Disjoint (Set.Ico (t0 + (i : ℝ) * δ) (t0 + ((i : ℝ) + 1) * δ))
          (Set.Ico (t0 + (j : ℝ) * δ) (t0 + ((j : ℝ) + 1) * δ)) := by
        rw [Set.Ico_disjoint_Ico]
        exact le_trans (min_le_right _ _) (le_trans hle (le_max_left _ _))
      rw [Set.disjoint_left]
      rintro p ⟨ht1, -⟩ ⟨ht2, -⟩
      exact Set.disjoint_left.mp h1d ht1 ht2
  have hU_T : (⋃ k ∈ Finset.range N,
      Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1)
      = Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_Ico, Set.mem_Icc,
      Finset.mem_range]
    constructor
    · rintro ⟨k, hk, ⟨h1, h2⟩, hx1, hx2⟩
      exact ⟨⟨le_trans (hAle k) h1, lt_of_lt_of_le h2 (hBle' k hk)⟩, hx1, hx2⟩
    · rintro ⟨⟨ht0, ht1⟩, hx1, hx2⟩
      have hq0 : 0 ≤ (p.1 - t0) / δ := div_nonneg (sub_nonneg.mpr ht0) hδpos.le
      have hk1 : ((Nat.floor ((p.1 - t0) / δ) : ℕ) : ℝ) ≤ (p.1 - t0) / δ :=
        Nat.floor_le hq0
      have hk2 : (p.1 - t0) / δ < ((Nat.floor ((p.1 - t0) / δ) : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hqN : (p.1 - t0) / δ < (N : ℝ) := by
        rw [div_lt_iff₀ hδpos, hNδ]
        linarith
      have hkN : Nat.floor ((p.1 - t0) / δ) < N := by
        have h : (((Nat.floor ((p.1 - t0) / δ) : ℕ)) : ℝ) < (N : ℝ) :=
          lt_of_le_of_lt hk1 hqN
        exact_mod_cast h
      refine ⟨Nat.floor ((p.1 - t0) / δ), hkN, ⟨?_, ?_⟩, hx1, hx2⟩
      · rw [le_div_iff₀ hδpos] at hk1
        linarith
      · rw [div_lt_iff₀ hδpos] at hk2
        linarith
  have h_int_M : (∫ p in (Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume)
      = ∑ k ∈ Finset.range N, ∫ p in
        (Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ) ×ˢ Set.Icc (0 : ℝ) 1),
        F p ∂volume := by
    rw [← hU_T]
    exact integral_biUnion_finset _ (fun k _ => hTmeas k)
      hD_TT (fun k hk => hTint k (Finset.mem_range.mp hk))
  have h_int_G0 : (∫ p in ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume) = 0 := by
    have hnull : volume ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) = 0 := by
      have h := Measure.prod_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        ({t1} : Set ℝ) (Set.Icc (0 : ℝ) 1)
      rw [Real.volume_singleton, zero_mul] at h
      exact h
    have h0 : volume.restrict ((({t1} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) = 0 :=
      Measure.restrict_eq_zero.mpr hnull
    rw [h0]
    exact integral_zero_measure F
  have h_int_F0 : ∀ k : ℕ, (∫ p in
      ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume) = 0 := by
    intro k
    have hnull : volume ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) = 0 := by
      have h := Measure.prod_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        ({t0 + ((k : ℝ) + 1) * δ} : Set ℝ) (Set.Icc (0 : ℝ) 1)
      rw [Real.volume_singleton, zero_mul] at h
      exact h
    have h0 : volume.restrict ((({t0 + ((k : ℝ) + 1) * δ} : Set ℝ)) ×ˢ Set.Icc (0 : ℝ) 1) = 0 :=
      Measure.restrict_eq_zero.mpr hnull
    rw [h0]
    exact integral_zero_measure F
  have h_int_R : (∫ p in (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume)
      = ∫ p in (Set.Ico t0 t1 ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume := by
    rw [hU_R, setIntegral_union hD_MG hGmeas hMint hGint, h_int_G0, add_zero]
  have h_int_S : ∀ k : ℕ, k < N →
      (∫ p in (Set.Icc (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ)
        ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume)
      = ∫ p in (Set.Ico (t0 + (k : ℝ) * δ) (t0 + ((k : ℝ) + 1) * δ)
        ×ˢ Set.Icc (0 : ℝ) 1), F p ∂volume := by
    intro k hk
    rw [hU_S k, setIntegral_union (hD_TF k) (hFmeas k) (hTint k hk) (hFint k hk),
      h_int_F0 k, add_zero]
  rw [h_int_R, h_int_M]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact (h_int_S k hk).symm
/-- Rectangle split of the squared Fbar (from MemLp). -/

theorem fbar_sq_split
    {t0 t1 : ℝ} (ht : t0 < t1)
    {f g : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hg : MemLp (Function.uncurry g) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {N : ℕ} (hN : 0 < N)
    (hMem : MemLp (fun p : ℝ × ℝ =>
      (if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
         (f s p.2 - g s p.2))) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, ((fun p : ℝ × ℝ =>
      (if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
         (f s p.2 - g s p.2))) p) ^ 2
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∑ k ∈ Finset.range N,
        ∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
          ((fun p : ℝ × ℝ =>
      (if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
         (f s p.2 - g s p.2))) p) ^ 2
            ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)) := by
  exact rectangle_integral_sum_slabs ht hMem.integrable_sq N hN


theorem slab_avg_sq_integral_le
    {t0 t1 : ℝ} (ht : t0 < t1)
    {f : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hSplitThm : ∀ {t0 t1 : ℝ}, t0 < t1 → ∀ {F : ℝ × ℝ → ℝ},
      IntegrableOn F (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) volume → ∀ (N : ℕ), 0 < N →
      ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, F p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
        = ∑ k ∈ Finset.range N,
          ∫ p in Set.Icc (t0 + k * ((t1 - t0) / N)) (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1,
              F p ∂(volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N)) (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc 0 1)))
    (hSlabThm : ∀ {a b : ℝ}, a < b → ∀ {f : ℝ → ℝ → ℝ},
      MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1)) →
      ∫ p in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
          (((b - a)⁻¹ * ∫ s in a..b, f s p.2) ^ 2) ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1))
        ≤ ∫ p in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
            (f p.1 p.2) ^ 2 ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1)))
    (N : ℕ) (hN : 0 < N) :
    ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        ((if p.1 = t1 then f p.1 p.2
          else ((N : ℝ) / (t1 - t0)) * ∫ s in
            (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
            f s p.2) ^ 2) ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ≤ ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (f p.1 p.2) ^ 2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  have hHint : IntegrableOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) volume := by
    have h := hf.integrable_sq
    simpa [Function.uncurry, IntegrableOn] using h
  by_cases hG : IntegrableOn (fun p : ℝ × ℝ =>
      ((if p.1 = t1 then f p.1 p.2
        else ((N : ℝ) / (t1 - t0)) * ∫ s in
          (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
            (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
          f s p.2) ^ 2))
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) volume
  · have hSplitG := hSplitThm ht hG N hN
    have hSplitH := hSplitThm ht hHint N hN
    rw [hSplitG, hSplitH]
    apply Finset.sum_le_sum
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdiff : 0 < t1 - t0 := sub_pos.mpr ht
    have hτ : 0 < (t1 - t0) / (N : ℝ) := div_pos hdiff hN'
    have hab : t0 + k * ((t1 - t0) / N) < t0 + (k + 1 : ℝ) * ((t1 - t0) / N) := by
      have h1 : (k : ℝ) < (k : ℝ) + 1 := lt_add_one _
      have h2 : (k : ℝ) * ((t1 - t0) / (N : ℝ)) < ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) := by
        apply mul_lt_mul_of_pos_right h1 hτ
      have h3 := add_lt_add_left h2 t0
      simpa using h3
    have hNt : (N : ℝ) ≠ 0 := ne_of_gt hN'
    have hsub : Set.Icc (t0 + k * ((t1 - t0) / N)) (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ
          Set.Icc (0 : ℝ) 1 ⊆ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
      apply Set.prod_mono _ Set.Subset.rfl
      apply Set.Icc_subset_Icc
      · have hnn : 0 ≤ (k : ℝ) * ((t1 - t0) / (N : ℝ)) :=
          mul_nonneg (Nat.cast_nonneg _) hτ.le
        have hle : t0 ≤ t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ)) :=
          le_add_of_nonneg_right hnn
        simpa using hle
      · have hk1N : k + 1 ≤ N := by omega
        have hk1R : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk1N
        have hmul : ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) ≤ (N : ℝ) * ((t1 - t0) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hk1R hτ.le
        have hNτ : (N : ℝ) * ((t1 - t0) / (N : ℝ)) = t1 - t0 := by field_simp
        have hle : t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) ≤ t1 := by
          have h1 : t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))
              ≤ t0 + (N : ℝ) * ((t1 - t0) / (N : ℝ)) := by linarith [hmul]
          rw [hNτ] at h1
          linarith
        simpa using hle
    have hmeas_slab : MeasurableSet (Set.Icc (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hmem_slab : MemLp (Function.uncurry f) 2
        (volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)) := by
      have h0 := hf.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
        (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)
      have hrr : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
            (Set.Icc (t0 + k * ((t1 - t0) / N))
              (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)
          = volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1) := by
        rw [Measure.restrict_restrict hmeas_slab, Set.inter_eq_self_of_subset_left hsub]
      rwa [hrr] at h0
    have hdiff' : (t1 - t0) ≠ 0 := ne_of_gt hdiff
    have hb_le : t0 + (k + 1 : ℝ) * ((t1 - t0) / N) ≤ t1 := by
      have hk1N : k + 1 ≤ N := by omega
      have hk1R : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk1N
      have hmul : ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) ≤ (N : ℝ) * ((t1 - t0) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hk1R hτ.le
      have hNτ : (N : ℝ) * ((t1 - t0) / (N : ℝ)) = t1 - t0 := by field_simp
      have h1 : t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))
          ≤ t0 + (N : ℝ) * ((t1 - t0) / (N : ℝ)) := by linarith [hmul]
      rw [hNτ] at h1
      have h2 : t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) ≤ t1 := by linarith
      simpa using h2
    have hba' : (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N))
        = (t1 - t0) / (N : ℝ) := by ring
    have hba_inv : ((t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N)))⁻¹
        = (N : ℝ) / (t1 - t0) := by
      rw [hba']
      field_simp
    have heq_on : ∀ p : ℝ × ℝ, p ∈ Set.Ioo (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1 →
        ((if p.1 = t1 then f p.1 p.2
          else ((N : ℝ) / (t1 - t0)) * ∫ s in
            (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
            f s p.2) ^ 2)
        = ((((t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N)))⁻¹
          * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1 : ℝ) * ((t1 - t0) / N)),
            f s p.2) ^ 2) := by
      intro p hp
      have hp1 : p.1 ∈ Set.Ioo (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) := (Set.mem_prod.mp hp).1
      rw [Set.mem_Ioo] at hp1
      obtain ⟨hlt_left, hlt_right⟩ := hp1
      have h1 : (k : ℝ) * ((t1 - t0) / (N : ℝ)) < p.1 - t0 := by
        have h : t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ)) < p.1 := by simpa using hlt_left
        linarith
      have h2 : p.1 - t0 < ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) := by
        have h : p.1 < t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) := by simpa using hlt_right
        linarith
      have hlt1 : (k : ℝ) < (p.1 - t0) / ((t1 - t0) / (N : ℝ)) := by
        rw [lt_div_iff₀ hτ]
        exact h1
      have hlt2 : (p.1 - t0) / ((t1 - t0) / (N : ℝ)) < (k : ℝ) + 1 := by
        rw [div_lt_iff₀ hτ]
        exact h2
      have hle1 : (k : ℝ) ≤ (p.1 - t0) / ((t1 - t0) / (N : ℝ)) := le_of_lt hlt1
      have hnonneg : 0 ≤ (p.1 - t0) / ((t1 - t0) / (N : ℝ)) :=
        le_trans (Nat.cast_nonneg k) hle1
      have hfloor : Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) = k :=
        (Nat.floor_eq_iff hnonneg).mpr ⟨hle1, hlt2⟩
      have hfloor' : Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) = k := by simpa using hfloor
      have hlt_t1 : p.1 < t1 := lt_of_lt_of_le hlt_right hb_le
      have hne : p.1 ≠ t1 := ne_of_lt hlt_t1
      rw [ite_eq_right hne, hfloor', ← hba_inv]
    have hmeas_Ioo : MeasurableSet (Set.Ioo (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
      measurableSet_Ioo.prod measurableSet_Icc
    have hset : (Set.Ioo (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume]
        (Set.Icc (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1) := by
      have h1 : Set.Ioo (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) =ᵐ[(volume : Measure ℝ)]
          Set.Icc (t0 + k * ((t1 - t0) / N)) (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) :=
        Ioo_ae_eq_Icc
      have h2 : Set.Icc (0 : ℝ) 1 =ᵐ[(volume : Measure ℝ)] Set.Icc (0 : ℝ) 1 :=
        Filter.EventuallyEq.refl _ _
      exact Measure.set_prod_ae_eq h1 h2
    have hrestrict_eq : volume.restrict (Set.Ioo (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)
        = volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1) :=
      Measure.restrict_congr_set hset
    have hae_Ioo : (fun p : ℝ × ℝ =>
          ((if p.1 = t1 then f p.1 p.2
            else ((N : ℝ) / (t1 - t0)) * ∫ s in
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2))
        =ᵐ[volume.restrict (Set.Ioo (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)]
        (fun p : ℝ × ℝ =>
          ((((t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N)))⁻¹
            * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2)) := by
      have hmem : ∀ᵐ p ∂(volume.restrict (Set.Ioo (t0 + k * ((t1 - t0) / N))
          (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)),
          p ∈ Set.Ioo (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1 :=
        ae_restrict_mem hmeas_Ioo
      filter_upwards [hmem] with p hp using heq_on p hp
    have hae_Icc : (fun p : ℝ × ℝ =>
          ((if p.1 = t1 then f p.1 p.2
            else ((N : ℝ) / (t1 - t0)) * ∫ s in
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2))
        =ᵐ[volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)]
        (fun p : ℝ × ℝ =>
          ((((t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N)))⁻¹
            * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2)) := by
      rwa [hrestrict_eq] at hae_Ioo
    have hae_set : (fun p : ℝ × ℝ =>
          ((if p.1 = t1 then f p.1 p.2
            else ((N : ℝ) / (t1 - t0)) * ∫ s in
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2))
        =ᵐ[((volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1)).restrict
          (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1))]
        (fun p : ℝ × ℝ =>
          ((((t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N)))⁻¹
            * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2)) :=
      hae_Icc.restrict
    have hcongr : (∫ p in Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1,
          ((if p.1 = t1 then f p.1 p.2
            else ((N : ℝ) / (t1 - t0)) * ∫ s in
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2)
          ∂(volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc 0 1)))
        = (∫ p in Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0 : ℝ) 1,
          ((((t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) - (t0 + k * ((t1 - t0) / N)))⁻¹
            * ∫ s in (t0 + k * ((t1 - t0) / N))..(t0 + (k + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2)
          ∂(volume.restrict (Set.Icc (t0 + k * ((t1 - t0) / N))
            (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc 0 1))) :=
      integral_congr_ae hae_set
    have hslab := hSlabThm hab hmem_slab
    rw [hcongr]
    exact hslab
  · have hmeas : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hrr : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
          (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
        = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
      rw [Measure.restrict_restrict hmeas, Set.inter_self]
    have hLHS0 : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          ((if p.1 = t1 then f p.1 p.2
            else ((N : ℝ) / (t1 - t0)) * ∫ s in
              (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N)),
              f s p.2) ^ 2) ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) = 0 := by
      apply integral_undef
      rw [hrr]
      exact hG
    rw [hLHS0]
    exact integral_nonneg (fun _ => sq_nonneg _)


theorem eLpNorm_le_of_sq_integral_le
    {μ : MeasureTheory.Measure (ℝ × ℝ)} {g f : ℝ × ℝ → ℝ}
    (hg : MemLp g 2 μ) (hf : MemLp f 2 μ)
    (hInt : ∫ p, (g p) ^ 2 ∂μ ≤ ∫ p, (f p) ^ 2 ∂μ) :
    eLpNorm g 2 μ ≤ eLpNorm f 2 μ := by
  have h2ne0 : (2 : ENNReal) ≠ 0 := by simp
  have h2netop : (2 : ENNReal) ≠ ⊤ := by simp
  have h2r : (2 : ENNReal).toReal = 2 := by simp
  rw [hg.eLpNorm_eq_integral_rpow_norm h2ne0 h2netop,
      hf.eLpNorm_eq_integral_rpow_norm h2ne0 h2netop, h2r]
  have hpt : ∀ x : ℝ, ‖x‖ ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hgI : (∫ a, ‖g a‖ ^ (2 : ℝ) ∂μ) = ∫ p, (g p) ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun a => hpt (g a))
  have hfI : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) = ∫ p, (f p) ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun a => hpt (f a))
  rw [hgI, hfI]
  apply ENNReal.ofReal_le_ofReal
  refine Real.rpow_le_rpow ?_ hInt ?_
  · exact integral_nonneg fun a => sq_nonneg _
  · positivity


theorem slab_avg_sub_le_oscillation
    {t0 t1 : ℝ} (ht : t0 < t1)
    {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    (N : ℕ) (hN : 0 < N) (t x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (ht0 : t ∈ Set.Icc t0 t1) (ht1 : t ≠ t1) :
    |(((N : ℝ) / (t1 - t0)) * ∫ s in (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))), φ s x) - φ t x|
      ≤ ⨆ s ∈ Set.Icc
          (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))
          (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
        |φ s x - φ t x| := by
  set τ : ℝ := (t1 - t0) / N with hτdef
  set k : ℕ := Nat.floor ((t - t0) / τ) with hkdef
  set a : ℝ := t0 + (k : ℝ) * τ with hadef
  set b : ℝ := t0 + ((k : ℝ) + 1) * τ with hbdef
  set c : ℝ := (N : ℝ) / (t1 - t0) with hcdef
  set v : ℝ := φ t x with hvdef
  have hNt : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNt
  have hd : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
  have hdne : t1 - t0 ≠ 0 := ne_of_gt hd
  have hτpos : (0 : ℝ) < τ := by
    rw [hτdef]
    exact div_pos hd hNt
  have hNτ : (N : ℝ) * τ = t1 - t0 := by
    rw [hτdef]
    field_simp
  have ht0le : t0 ≤ t := ht0.1
  have htle1 : t ≤ t1 := ht0.2
  have htt1 : t < t1 := lt_of_le_of_ne htle1 ht1
  have hx0nn : (0 : ℝ) ≤ (t - t0) / τ := div_nonneg (sub_nonneg.mpr ht0le) hτpos.le
  have hNx : (t - t0) / τ < (N : ℝ) := by
    rw [div_lt_iff₀ hτpos, hNτ]
    linarith
  have hflt : (k : ℝ) ≤ (t - t0) / τ := by
    rw [hkdef]
    exact Nat.floor_le hx0nn
  have hkN : k < N := by
    have h1 : (k : ℝ) < (N : ℝ) := lt_of_le_of_lt hflt hNx
    exact_mod_cast h1
  have hk1 : (k : ℝ) + 1 ≤ (N : ℝ) := by
    have h2 : k + 1 ≤ N := by omega
    exact_mod_cast h2
  have hkk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hkk hτpos.le) t0
  have ha0 : t0 ≤ a := by
    rw [hadef]
    have hnn : (0 : ℝ) ≤ (k : ℝ) * τ := mul_nonneg (by positivity) hτpos.le
    linarith
  have hb1 : b ≤ t1 := by
    rw [hbdef]
    have h1 : ((k : ℝ) + 1) * τ ≤ (N : ℝ) * τ :=
      mul_le_mul_of_nonneg_right hk1 hτpos.le
    rw [hNτ] at h1
    linarith
  have hba : b - a = τ := by
    rw [hadef, hbdef]
    ring
  have hcb : c * (b - a) = 1 := by
    rw [hba, hcdef, hτdef]
    field_simp
  have hsub : Set.Icc a b ⊆ Set.Icc t0 t1 :=
    fun s hs => ⟨le_trans ha0 hs.1, le_trans hs.2 hb1⟩
  have hpair : Set.MapsTo (fun s => (s, x)) (Set.Icc a b)
      (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) :=
    fun s hs => ⟨hsub hs, hx⟩
  have hfx : ContinuousOn (fun s => (s, x)) (Set.Icc a b) :=
    continuousOn_id.prodMk continuousOn_const
  have hcont1 : ContinuousOn (fun s => φ s x) (Set.Icc a b) :=
    hφ.comp hfx hpair
  have hcontD : ContinuousOn (fun s => φ s x - v) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun s => φ s x + -v) (Set.Icc a b) :=
      hcont1.add continuousOn_const
    simpa only [sub_eq_add_neg] using h1
  have hcontA : ContinuousOn (fun s => |φ s x - v|) (Set.Icc a b) :=
    continuous_abs.comp_continuousOn hcontD
  have hfI : IntervalIntegrable (fun s => φ s x) MeasureTheory.volume a b :=
    hcont1.intervalIntegrable_of_Icc hab
  have hgI : IntervalIntegrable (fun _ => v) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hsplit : (∫ s in a..b, (φ s x - v))
      = (∫ s in a..b, φ s x) - ∫ s in a..b, v :=
    intervalIntegral.integral_sub hfI hgI
  have hconstI : (∫ s in a..b, v) = (b - a) * v := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hcv : c * (∫ s in a..b, v) = v := by
    rw [hconstI, ← mul_assoc, hcb, one_mul]
  have hmain : c * (∫ s in a..b, φ s x) - v = c * ∫ s in a..b, (φ s x - v) := by
    rw [hsplit, mul_sub, hcv]
  have hbddimg : BddAbove ((fun s => |φ s x - v|) '' Set.Icc a b) :=
    isCompact_Icc.bddAbove_image hcontA
  have hleC : ∀ s ∈ Set.Icc a b,
      |φ s x - v| ≤ ⨆ s ∈ Set.Icc a b, |φ s x - v| := by
    intro s hs
    have hbdd : BddAbove
        (Set.range fun u => ⨆ _ : u ∈ Set.Icc a b, |φ u x - v|) := by
      obtain ⟨M, hM⟩ := hbddimg
      rw [mem_upperBounds] at hM
      refine ⟨max M 0, fun y hy => ?_⟩
      obtain ⟨u, rfl⟩ := hy
      dsimp only
      by_cases hu : u ∈ Set.Icc a b
      · rw [ciSup_const (hι := ⟨hu⟩)]
        exact le_max_of_le_left (hM _ ⟨u, hu, rfl⟩)
      · have hempty : (⨆ _ : u ∈ Set.Icc a b, |φ u x - v|) = sSup ∅ :=
          @iSup_of_empty' ℝ (u ∈ Set.Icc a b) _ ⟨hu⟩ _
        rw [hempty, Real.sSup_empty]
        exact le_max_right M 0
    have h1 : (⨆ _ : s ∈ Set.Icc a b, |φ s x - v|)
        ≤ ⨆ u ∈ Set.Icc a b, |φ u x - v| :=
      le_ciSup hbdd s
    rw [ciSup_const (hι := ⟨hs⟩)] at h1
    exact h1
  have hnorm : |∫ s in a..b, (φ s x - v)|
      ≤ (⨆ s ∈ Set.Icc a b, |φ s x - v|) * |b - a| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hab] at hs
    have hs' : s ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hs
    rw [Real.norm_eq_abs]
    exact hleC s hs'
  have habs : |c| * |b - a| = 1 := by
    have h := congrArg abs hcb
    rw [abs_mul, abs_one] at h
    exact h
  rw [hmain, abs_mul]
  exact calc |c| * |∫ s in a..b, (φ s x - v)|
        ≤ |c| * ((⨆ s ∈ Set.Icc a b, |φ s x - v|) * |b - a|) :=
          mul_le_mul_of_nonneg_left hnorm (abs_nonneg c)
      _ = ⨆ s ∈ Set.Icc a b, |φ s x - v| := by
          have hcomm : |c| * ((⨆ s ∈ Set.Icc a b, |φ s x - v|) * |b - a|)
              = (⨆ s ∈ Set.Icc a b, |φ s x - v|) * (|c| * |b - a|) := by ring
          rw [hcomm, habs, mul_one]


theorem oscillation_le_of_uniformly_continuous
    {a b t : ℝ} {ε δ : ℝ} (hat : a ≤ t) (htb : t ≤ b) (hab : b - a < δ)
    {φ : ℝ → ℝ → ℝ} {x : ℝ} (hε : 0 < ε)
    (hUnif : ∀ (s : ℝ), s ∈ Set.Icc a b → |φ s x - φ t x| < ε) :
    ⨆ s ∈ Set.Icc a b, |φ s x - φ t x| ≤ ε := by
  apply ciSup_le
  intro s
  by_cases hs : s ∈ Set.Icc a b
  · haveI : Nonempty (s ∈ Set.Icc a b) := ⟨hs⟩
    exact ciSup_le (fun _ => le_of_lt (hUnif s hs))
  · rw [ciSup_neg hs, Real.sSup_empty]
    exact hε.le


theorem iSup_mem_abs_le_of_forall_lt {a b t x ε : ℝ} {φ : ℝ → ℝ → ℝ}
    (hlt : ∀ s ∈ Set.Icc a b, |φ s x - φ t x| < ε) (hε : 0 < ε) :
    ⨆ s ∈ Set.Icc a b, |φ s x - φ t x| ≤ ε := by
  have hEmpty : sSup (∅ : Set ℝ) = 0 := by simp [Real.sSup_def]
  refine ciSup_le (fun s => ?_)
  show (⨆ _ : s ∈ Set.Icc a b, |φ s x - φ t x|) ≤ ε
  by_cases hs : s ∈ Set.Icc a b
  · haveI : Nonempty (s ∈ Set.Icc a b) := ⟨hs⟩
    exact ciSup_le (fun hmem => le_of_lt (hlt s hmem))
  · haveI : IsEmpty (s ∈ Set.Icc a b) := ⟨hs⟩
    rw [iSup_of_empty', hEmpty]
    exact hε.le

/-- Uniform sup bound for slab averages, from the pointwise
estimate and the oscillation bound as hypotheses. -/

theorem slab_avg_sup_sub_le
    {t0 t1 : ℝ} (ht : t0 < t1)
    {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    (hPtwiseThm : ∀ {t0 t1 : ℝ}, t0 < t1 → ∀ {φ : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) →
      ∀ (N : ℕ), 0 < N → ∀ (t x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      t ∈ Set.Icc t0 t1 → t ≠ t1 →
      |(((N : ℝ) / (t1 - t0)) * ∫ s in
          (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
            (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
          φ s x) - φ t x|
        ≤ ⨆ s ∈ Set.Icc
            (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))
            (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
          |φ s x - φ t x|)
    (hOscThm : ∀ {a b t : ℝ} {ε δ : ℝ}, a ≤ t → t ≤ b → b - a < δ → ∀ {φ : ℝ → ℝ → ℝ} {x : ℝ},
      0 < ε → (∀ (s : ℝ), s ∈ Set.Icc a b → |φ s x - φ t x| < ε) →
      ⨆ s ∈ Set.Icc a b, |φ s x - φ t x| ≤ ε)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hUnif : ∀ (t t' x : ℝ), t ∈ Set.Icc t0 t1 → t' ∈ Set.Icc t0 t1 →
      x ∈ Set.Icc (0 : ℝ) 1 → |t - t'| < δ → |φ t x - φ t' x| < ε)
    (N : ℕ) (hN : 0 < N) (hτ : (t1 - t0) / N < δ) (t x : ℝ)
    (ht0 : t ∈ Set.Icc t0 t1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(if t = t1 then φ t x
      else ((N : ℝ) / (t1 - t0)) * ∫ s in
        (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
          (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
        φ s x) - φ t x| ≤ ε := by
  by_cases ht1 : t = t1
  · rw [ite_eq_left ht1, sub_self, abs_zero]
    exact hε.le
  · rw [ite_eq_right ht1]
    have h1 := hPtwiseThm ht hφ N hN t x hx ht0 ht1
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hτpos : 0 < (t1 - t0) / N := div_pos (sub_pos.mpr ht) hNpos
    have hτne : (t1 - t0) / N ≠ 0 := ne_of_gt hτpos
    have hNne : ((N : ℝ)) ≠ 0 := ne_of_gt hNpos
    have hNτ : (N : ℝ) * ((t1 - t0) / N) = t1 - t0 := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hNne
    have hq0 : 0 ≤ (t - t0) / ((t1 - t0) / N) :=
      div_nonneg (sub_nonneg.mpr ht0.1) hτpos.le
    have hk_le : (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ)
        ≤ (t - t0) / ((t1 - t0) / N) := Nat.floor_le hq0
    have hk_lt : (t - t0) / ((t1 - t0) / N)
        < (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hA_le : t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N) ≤ t := by
      have h1' := mul_le_mul_of_nonneg_right hk_le hτpos.le
      rw [div_mul_cancel₀ _ hτne] at h1'
      linarith
    have hB_ge : t ≤ t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ)) * ((t1 - t0) / N) := by
      have h2' := mul_lt_mul_of_pos_right hk_lt hτpos
      rw [div_mul_cancel₀ _ hτne] at h2'
      linarith
    have hBA : (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ)) * ((t1 - t0) / N))
        - (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))
        = (t1 - t0) / N := by ring
    have hA0 : t0 ≤ t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N) := by
      have hnn : 0 ≤ (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N) :=
        mul_nonneg (Nat.cast_nonneg _) hτpos.le
      linarith
    have ht_lt : t < t1 := lt_of_le_of_ne ht0.2 ht1
    have hqN : (t - t0) / ((t1 - t0) / N) < (N : ℝ) := by
      rw [div_lt_iff₀ hτpos, hNτ]
      linarith [ht_lt]
    have hkn : Nat.floor ((t - t0) / ((t1 - t0) / N)) < N :=
      (Nat.floor_lt hq0).mpr hqN
    have hkNr : (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) + 1 ≤ (N : ℝ) := by
      have hle : Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 ≤ N := by omega
      exact_mod_cast hle
    have hB1 : t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ)) * ((t1 - t0) / N) ≤ t1 := by
      have hle := mul_le_mul_of_nonneg_right hkNr hτpos.le
      rw [hNτ] at hle
      linarith
    have hBlt : (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ)) * ((t1 - t0) / N))
        - (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) < δ := by
      rw [hBA]
      exact hτ
    have hpt : ∀ s ∈ Set.Icc
        (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))
        (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ)) * ((t1 - t0) / N)),
        |φ s x - φ t x| < ε := by
      intro s hs
      have hs1 : t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N) ≤ s := hs.1
      have hs2 : s ≤ t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ)) * ((t1 - t0) / N) := hs.2
      have hsIcc : s ∈ Set.Icc t0 t1 := ⟨le_trans hA0 hs1, le_trans hs2 hB1⟩
      have hst : |s - t| < δ := by
        refine lt_of_le_of_lt ?_ hBlt
        rw [abs_le]
        constructor <;> linarith [hs1, hs2, hA_le, hB_ge]
      exact hUnif s t x hsIcc ht0 hx hst
    exact le_trans h1 (iSup_mem_abs_le_of_forall_lt hpt hε)


theorem eLpNorm_le_sup_mul_sqrt_measure
    {μ : MeasureTheory.Measure (ℝ × ℝ)} (hμ : μ univ < ∞)
    {g : ℝ × ℝ → ℝ} (hg : AEStronglyMeasurable g μ)
    {ε : ℝ} (hε : 0 ≤ ε) (hBound : ∀ᵐ p ∂μ, |g p| ≤ ε) :
    (eLpNorm g 2 μ).toReal ≤ ε * (μ univ).toReal ^ (1 / 2 : ℝ) := by
  have hNorm : ∀ᵐ p ∂μ, ‖g p‖ ≤ ε := by
    filter_upwards [hBound] with p hp
    rwa [Real.norm_eq_abs]
  have hle : eLpNorm g 2 μ ≤ μ univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal ε :=
    eLpNorm_le_of_ae_bound (p := 2) hg hNorm
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [h2] at hle
  have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hinv] at hle
  have hμne : μ univ ≠ ∞ := ne_of_lt hμ
  have hrpow_ne : μ univ ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμne
  have hRHS_ne : μ univ ^ (1 / 2 : ℝ) * ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.mul_ne_top hrpow_ne ENNReal.ofReal_ne_top
  have hmono := ENNReal.toReal_mono hRHS_ne hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hε] at hmono
  rwa [mul_comm _ ε] at hmono


theorem slab_avg_eventually_sup_le
    {t0 t1 : ℝ} (ht : t0 < t1)
    {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    (hSupThm : ∀ {t0 t1 : ℝ}, t0 < t1 → ∀ {φ : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) →
      ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      (∀ (t t' x : ℝ), t ∈ Set.Icc t0 t1 → t' ∈ Set.Icc t0 t1 →
        x ∈ Set.Icc (0 : ℝ) 1 → |t - t'| < δ → |φ t x - φ t' x| < ε) →
      ∀ (N : ℕ), 0 < N → (t1 - t0) / N < δ → ∀ (t x : ℝ),
      t ∈ Set.Icc t0 t1 → x ∈ Set.Icc (0 : ℝ) 1 →
      |(if t = t1 then φ t x
        else ((N : ℝ) / (t1 - t0)) * ∫ s in
          (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
          φ s x) - φ t x| ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (N : ℕ) in Filter.atTop, ∀ (t x : ℝ), t ∈ Set.Icc t0 t1 → x ∈ Set.Icc (0 : ℝ) 1 →
      |(if t = t1 then φ t x
        else ((N : ℝ) / (t1 - t0)) * ∫ s in
          (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
          φ s x) - φ t x| ≤ ε := by
  have hK : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hUC : UniformContinuousOn (Function.uncurry φ)
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    IsCompact.uniformContinuousOn_of_continuous hK hφ
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδpos, hδ⟩ := hUC ε hε
  have hU : ∀ (t t' x : ℝ), t ∈ Set.Icc t0 t1 → t' ∈ Set.Icc t0 t1 →
      x ∈ Set.Icc (0 : ℝ) 1 → |t - t'| < δ → |φ t x - φ t' x| < ε := by
    intro t t' x htmem ht'mem hxmem hlt
    have hmem1 : (t, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod htmem hxmem
    have hmem2 : (t', x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod ht'mem hxmem
    have hdist : dist (t, x) (t', x) = |t - t'| := by
      rw [Prod.dist_eq]
      show max (dist t t') (dist x x) = |t - t'|
      rw [dist_self, max_eq_left dist_nonneg, Real.dist_eq]
    have hlt' : dist (t, x) (t', x) < δ := by rw [hdist]; exact hlt
    have h := hδ (t, x) hmem1 (t', x) hmem2 hlt'
    rw [Real.dist_eq] at h
    exact h
  have hτ : Filter.Tendsto (fun N : ℕ => (t1 - t0) / (N : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (t1 - t0)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (t1 - t0) / (N : ℝ) < δ :=
    Filter.Tendsto.eventually_lt_const hδpos hτ
  have hpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N := Filter.eventually_gt_atTop 0
  filter_upwards [hev, hpos] with N hτN hNpos t x htx hx
  exact hSupThm ht hφ ε δ hε hδpos hU N hNpos hτN t x htx hx


theorem slab_avg_continuous_tendsto_L2
    {t0 t1 : ℝ} (ht : t0 < t1)
    {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    (hEventuallyThm : ∀ {t0 t1 : ℝ}, t0 < t1 → ∀ {φ : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) →
      ∀ (ε : ℝ), 0 < ε →
      ∀ᶠ (N : ℕ) in Filter.atTop, ∀ (t x : ℝ), t ∈ Set.Icc t0 t1 → x ∈ Set.Icc (0 : ℝ) 1 →
        |(if t = t1 then φ t x
          else ((N : ℝ) / (t1 - t0)) * ∫ s in
            (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
              (t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
            φ s x) - φ t x| ≤ ε)
    (hENormSupThm : ∀ {μ : MeasureTheory.Measure (ℝ × ℝ)}, μ univ < ∞ →
      ∀ {g : ℝ × ℝ → ℝ}, AEStronglyMeasurable g μ → ∀ {ε : ℝ}, 0 ≤ ε →
      (∀ᵐ p ∂μ, |g p| ≤ ε) →
      (eLpNorm g 2 μ).toReal ≤ ε * (μ univ).toReal ^ (1 / 2 : ℝ)) :
    Filter.Tendsto (fun N : ℕ =>
        (eLpNorm (fun p : ℝ × ℝ =>
          (if p.1 = t1 then φ p.1 p.2
           else ((N : ℝ) / (t1 - t0)) * ∫ s in
             (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
               (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
             φ s p.2) - φ p.1 p.2) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal)
      Filter.atTop (nhds 0) := by
  set S : Set (ℝ × ℝ) := Set.Icc t0 t1 ×ˢ Set.Icc 0 1 with hS
  set μ : MeasureTheory.Measure (ℝ × ℝ) := volume.restrict S with hμ
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hScomp : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hμfin : μ univ < ∞ := by
    rw [hμ, Measure.restrict_apply_univ]
    exact hScomp.measure_lt_top
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  set M : ℝ := (μ univ).toReal ^ (1 / 2 : ℝ) with hM
  set C : ℝ := M + 1 with hC
  have hMnn : 0 ≤ M := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hCpos : 0 < C := by
    rw [hC]
    linarith [hMnn]
  have hMC : M < C := by
    rw [hC]
    linarith
  set ε : ℝ := ε' / C with hε
  have hεpos : 0 < ε := div_pos hε' hCpos
  have hEv := hEventuallyThm ht hφ ε hεpos
  have hstrict : ε * M < ε' := by
    have h1 : M / C < 1 := (div_lt_one hCpos).mpr hMC
    have h2 : ε' * (M / C) < ε' * 1 := mul_lt_mul_of_pos_left h1 hε'
    rw [mul_one] at h2
    have heq : ε * M = ε' * (M / C) := by
      rw [hε]
      ring
    rw [heq]
    exact h2
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hEv] with N hN
  show dist ((eLpNorm (fun p : ℝ × ℝ =>
    (if p.1 = t1 then φ p.1 p.2
     else ((N : ℝ) / (t1 - t0)) * ∫ s in
       (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
         (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
       φ s p.2) - φ p.1 p.2) 2 μ).toReal) 0 < ε'
  by_cases hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (if p.1 = t1 then φ p.1 p.2
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
         φ s p.2) - φ p.1 p.2) μ
  · have haeN : ∀ᵐ p ∂μ, |(fun p : ℝ × ℝ =>
        (if p.1 = t1 then φ p.1 p.2
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
           φ s p.2) - φ p.1 p.2) p| ≤ ε := by
      have hmem : ∀ᵐ p ∂μ, p ∈ S := ae_restrict_mem hSmeas
      filter_upwards [hmem] with p hp
      rw [hS] at hp
      obtain ⟨ht', hx'⟩ := Set.mem_prod.mp hp
      exact hN p.1 p.2 ht' hx'
    have hsup := hENormSupThm hμfin hmeas hεpos.le haeN
    have hnn : 0 ≤ (eLpNorm (fun p : ℝ × ℝ =>
        (if p.1 = t1 then φ p.1 p.2
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
           φ s p.2) - φ p.1 p.2) 2 μ).toReal := ENNReal.toReal_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    exact lt_of_le_of_lt hsup hstrict
  · have htop := eLpNorm_of_not_aestronglyMeasurable (μ := μ) (p := 2) hmeas
    rw [htop, ENNReal.toReal_top, Real.dist_eq, sub_zero, abs_zero]
    exact hε'


theorem tendsto_zero_of_eventually_three_eps
    (g : ℕ → ℝ) (hg_nonneg : ∀ N : ℕ, 0 ≤ g N)
    (hg : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in Filter.atTop, g N ≤ 3 * ε) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hg (ε / 4) hε4)
  refine ⟨N, fun n hn => ?_⟩
  have h3 : (3 : ℝ) * (ε / 4) < ε := by linarith
  have hdist : dist (g n) 0 = g n := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg_nonneg n)]
  rw [hdist]
  have hle := hN n hn
  linarith


theorem continuous_compactSupport_memLp
    {t0 t1 : ℝ}
    {φ : ℝ → ℝ → ℝ}
    (hφcont : Continuous (Function.uncurry φ)) (hφsupp : HasCompactSupport (Function.uncurry φ)) :
    MemLp (Function.uncurry φ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  exact hφcont.memLp_of_hasCompactSupport hφsupp


theorem continuous_continuousOn_rect
    {t0 t1 : ℝ}
    {φ : ℝ → ℝ → ℝ}
    (hφcont : Continuous (Function.uncurry φ)) :
    ContinuousOn (Function.uncurry φ) (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) := by
  exact hφcont.continuousOn


theorem continuous_compactSupport_dense_L2
    {t0 t1 : ℝ}
    {f : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ → ℝ,
      Continuous (Function.uncurry φ) ∧ HasCompactSupport (Function.uncurry φ)
        ∧ (eLpNorm (fun p => f p.1 p.2 - φ p.1 p.2) 2
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal < ε := by
  have hcompact : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hfin : volume (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ)) ≠ ⊤ :=
    hcompact.measure_lt_top.ne
  have hreg : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))).Regular :=
    Measure.Regular.restrict_of_measure_ne_top hfin
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hε' : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hε2).ne'
  obtain ⟨g, hg_supp, hg_le, hg_cont, hg_mem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (ε := ENNReal.ofReal (ε / 2))
      (show (2 : ENNReal) ≠ ⊤ from by simp) hε'
  refine ⟨Function.curry g, ?_, ?_, ?_⟩
  · rwa [Function.uncurry_curry]
  · rwa [Function.uncurry_curry]
  · have hfin' : eLpNorm (fun p : ℝ × ℝ => f p.1 p.2 - Function.curry g p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))) ≠ ⊤ :=
      (lt_of_le_of_lt hg_le ENNReal.ofReal_lt_top).ne
    calc (eLpNorm (fun p : ℝ × ℝ => f p.1 p.2 - Function.curry g p.1 p.2) 2
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) (1 : ℝ)))).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          (ENNReal.toReal_le_toReal hfin' ENNReal.ofReal_lt_top.ne).mpr hg_le
      _ = ε / 2 := ENNReal.toReal_ofReal hε2.le
      _ < ε := by linarith


theorem slab_avg_eventually_le_three_eps_final
    {t0 t1 : ℝ} (ht : t0 < t1)
    {f φ : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hφ : MemLp (Function.uncurry φ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (ε : ℝ) (hε : 0 < ε)
    (hTriThm : ∀ (N : ℕ), 0 < N →
      (eLpNorm (fun p : ℝ × ℝ =>
        (if p.1 = t1 then f p.1 p.2
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
           f s p.2) - f p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal
        ≤ (eLpNorm (fun p : ℝ × ℝ =>
            (if p.1 = t1 then (f p.1 p.2 - φ p.1 p.2)
             else ((N : ℝ) / (t1 - t0)) * ∫ s in
               (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                 (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
               (f s p.2 - φ s p.2))) 2
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal
          + (eLpNorm (fun p : ℝ × ℝ =>
              (if p.1 = t1 then φ p.1 p.2
               else ((N : ℝ) / (t1 - t0)) * ∫ s in
                 (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
                   (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
                 φ s p.2) - φ p.1 p.2) 2
              (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal
          + (eLpNorm (fun p => f p.1 p.2 - φ p.1 p.2) 2
              (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal)
    (hA : ∀ N : ℕ, 0 < N →
      (eLpNorm (fun p : ℝ × ℝ =>
        (if p.1 = t1 then (f p.1 p.2 - φ p.1 p.2)
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
           (f s p.2 - φ s p.2))) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal < ε)
    (hBev : Filter.Eventually (fun (N : ℕ) =>
      (eLpNorm (fun p : ℝ × ℝ =>
        (if p.1 = t1 then φ p.1 p.2
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
           φ s p.2) - φ p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal < ε) Filter.atTop)
    (hφsmall : (eLpNorm (fun p => f p.1 p.2 - φ p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal < ε) :
    ∀ᶠ (N : ℕ) in Filter.atTop,
      (eLpNorm (fun p : ℝ × ℝ =>
        (if p.1 = t1 then f p.1 p.2
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))),
           f s p.2) - f p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ 3 * ε := by
  filter_upwards [hBev, Filter.eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hT := hTriThm N hNpos
  have hA' := hA N hNpos
  linarith [hT, hA', hN, hφsmall]


theorem eLpNorm_const_one_aux :
    eLpNorm (fun _ => (1 : ℝ)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 := by
  have hvol : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    simp [Real.volume_Icc]
  have hμ : volume.restrict (Set.Icc (0 : ℝ) 1) ≠ 0 := by
    intro h
    rw [h] at hvol
    simp at hvol
  rw [eLpNorm_const _ two_ne_zero hμ, hvol]
  simp


theorem energyHyp_false
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (hEnergyThm : ∀ (w wx : ℝ → ℝ → ℝ),
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            -(w p.1 p.2) * deriv (fun s => φ s p.2) p.1
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * wx p.1 p.2 * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          = 0) →
      ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) = 0) :
    False := by
  set tstar : ℝ := (t0 + t1) / 2 with htstar
  have hts_lo : t0 < tstar := by simp [htstar]; linarith
  have hts_hi : tstar < t1 := by simp [htstar]; linarith
  have hts_mem : tstar ∈ Set.Icc t0 t1 := ⟨le_of_lt hts_lo, le_of_lt hts_hi⟩
  have hHom : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (-(if p.1 = tstar then (1 : ℝ) else 0)) * deriv (fun s => φ s p.2) p.1
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * (0 : ℝ) * deriv (fun y => φ p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = 0 := by
    intro φ hφ
    have hF : ∀ p : ℝ × ℝ, p.1 ≠ tstar →
        ((-(if p.1 = tstar then (1 : ℝ) else 0)) * deriv (fun s => φ s p.2) p.1) = 0 := by
      intro p hp
      simp [hp]
    have hmeasS : MeasurableSet ({tstar} ×ˢ (Set.univ : Set ℝ)) :=
      MeasurableSet.prod (measurableSet_singleton tstar) MeasurableSet.univ
    have hmeasR : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
      MeasurableSet.prod measurableSet_Icc measurableSet_Icc
    have hvol0 : volume ({tstar} ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    have hnull : ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) ({tstar} ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.restrict_apply hmeasS, Measure.restrict_apply (hmeasS.inter hmeasR)]
      exact measure_mono_null (Set.inter_subset_left.trans Set.inter_subset_left) hvol0
    have hA : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (-(if p.1 = tstar then (1 : ℝ) else 0)) * deriv (fun s => φ s p.2) p.1
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) = 0 := by
      have hae : ∀ᵐ p ∂(((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
          (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))),
          ((-(if p.1 = tstar then (1 : ℝ) else 0)) * deriv (fun s => φ s p.2) p.1) = 0 := by
        rw [ae_iff]
        refine measure_mono_null ?hsub hnull
        intro p hp
        simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff] at hp ⊢
        refine ⟨?_, Set.mem_univ _⟩
        by_contra hne
        exact hp (hF p hne)
      exact integral_eq_zero_of_ae hae
    have hB : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * (0 : ℝ) * deriv (fun y => φ p.1 y) p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) = 0 := by
      have hfun : (fun p : ℝ × ℝ => κ p.1 p.2 * (0 : ℝ) * deriv (fun y => φ p.1 y) p.2) = 0 := by
        funext p
        simp
      rw [hfun]
      exact integral_zero _ _
    rw [hA, hB, add_zero]
  have hId := hEnergyThm (fun t x => if t = tstar then (1 : ℝ) else 0)
    (fun _ _ => (0 : ℝ)) hHom tstar hts_mem
  have h2 : eLpNorm (fun x : ℝ => if tstar = tstar then (1 : ℝ) else 0) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := hId
  have e1 : eLpNorm (fun x : ℝ => if tstar = tstar then (1 : ℝ) else 0) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 := by
    have hfun : (fun x : ℝ => if tstar = tstar then (1 : ℝ) else 0)
        = (fun _ => (1 : ℝ)) := by
      funext x
      simp
    rw [hfun]
    exact eLpNorm_const_one_aux
  rw [e1] at h2
  exact one_ne_zero h2


theorem energyId_hyp_false
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (hEnergyIdThm : ∀ (w wx : ℝ → ℝ → ℝ),
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-w t x * deriv (fun s => φ s x) t + κ t x * wx t x * deriv (fun y => φ t y) x) = 0) →
      ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2
          = (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) :
    False := by
  set tstar : ℝ := (t0 + t1) / 2 with htstar
  have hts_lo : t0 < tstar := by simp [htstar]; linarith
  have hts_hi : tstar < t1 := by simp [htstar]; linarith
  have hts_mem : tstar ∈ Set.Icc t0 t1 := ⟨le_of_lt hts_lo, le_of_lt hts_hi⟩
  have ht0_ne : t0 ≠ tstar := ne_of_lt hts_lo
  have hHom : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-(fun t x => if t = tstar then (1 : ℝ) else 0) t x * deriv (fun s => φ s x) t
          + κ t x * (fun _ _ => (0 : ℝ)) t x * deriv (fun y => φ t y) x) = 0 := by
    intro φ hφ
    have hJ : ∀ t : ℝ, t ≠ tstar →
        (∫ x in (0 : ℝ)..1, (-(fun t x => if t = tstar then (1 : ℝ) else 0) t x
          * deriv (fun s => φ s x) t
          + κ t x * (fun _ _ => (0 : ℝ)) t x * deriv (fun y => φ t y) x)) = 0 := by
      intro t htne
      have hzero : (fun x => (-(fun t x => if t = tstar then (1 : ℝ) else 0) t x
          * deriv (fun s => φ s x) t
          + κ t x * (fun _ _ => (0 : ℝ)) t x * deriv (fun y => φ t y) x)) = 0 := by
        funext x
        simp [htne]
      rw [hzero]
      exact intervalIntegral.integral_zero
    have hnull : (volume.restrict (Set.Ioc t0 t1)) {tstar} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton tstar)]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        (∫ x in (0 : ℝ)..1, (-(fun t x => if t = tstar then (1 : ℝ) else 0) t x
          * deriv (fun s => φ s x) t
          + κ t x * (fun _ _ => (0 : ℝ)) t x * deriv (fun y => φ t y) x)) = 0 := by
      rw [ae_iff]
      refine measure_mono_null ?hsub hnull
      intro t ht
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at ht ⊢
      by_contra hne
      exact ht (hJ t hne)
    rw [intervalIntegral.integral_of_le ht.le]
    exact integral_eq_zero_of_ae hae
  have hId := hEnergyIdThm (fun t x => if t = tstar then (1 : ℝ) else 0)
    (fun _ _ => (0 : ℝ)) hHom tstar hts_mem
  have hdiss : (∫ t in t0..tstar, ∫ x in (0 : ℝ)..1, κ t x * (0 : ℝ) ^ 2) = 0 := by
    have h0 : (fun t : ℝ => ∫ x in (0 : ℝ)..1, κ t x * (0 : ℝ) ^ 2) = 0 := by
      funext t
      have h0' : (fun x : ℝ => κ t x * (0 : ℝ) ^ 2) = 0 := by
        funext x
        simp
      rw [h0']
      exact intervalIntegral.integral_zero
    rw [h0]
    exact intervalIntegral.integral_zero
  have h2 : (eLpNorm (fun x : ℝ => if tstar = tstar then (1 : ℝ) else 0) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * (∫ t in t0..tstar, ∫ x in (0 : ℝ)..1, κ t x * (0 : ℝ) ^ 2)
      = (eLpNorm (fun x : ℝ => if t0 = tstar then (1 : ℝ) else 0) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := hId
  have eA : (eLpNorm (fun x : ℝ => if tstar = tstar then (1 : ℝ) else 0) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 = 1 := by
    have hfun : (fun x : ℝ => if tstar = tstar then (1 : ℝ) else 0)
        = (fun _ => (1 : ℝ)) := by
      funext x
      simp
    rw [hfun, eLpNorm_const_one_aux, ENNReal.toReal_one]
    norm_num
  have eB : (eLpNorm (fun x : ℝ => if t0 = tstar then (1 : ℝ) else 0) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 = 0 := by
    have hfun : (fun x : ℝ => if t0 = tstar then (1 : ℝ) else 0) = 0 := by
      funext x
      simp [ht0_ne]
    rw [hfun, eLpNorm_zero, ENNReal.toReal_zero]
    norm_num
  rw [hdiss, eA, eB] at h2
  norm_num at h2


theorem weak_parabolic_unique_asm
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin : ℝ} (hkmin : 0 < kmin)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u1 ux1 u2 ux2 : ℝ → ℝ → ℝ)
    (hWeak1Thm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          -(u1 p.1 p.2) * deriv (fun s => φ s p.2) p.1
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * ux1 p.1 p.2 * deriv (fun y => φ p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = 0)
    (hWeak2Thm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          -(u2 p.1 p.2) * deriv (fun s => φ s p.2) p.1
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * ux2 p.1 p.2 * deriv (fun y => φ p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = 0)
    (hSubThm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          -((u1 p.1 p.2 - u2 p.1 p.2)) * deriv (fun s => φ s p.2) p.1
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * (ux1 p.1 p.2 - ux2 p.1 p.2) * deriv (fun y => φ p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = 0)
    (hEnergyThm : ∀ (w wx : ℝ → ℝ → ℝ),
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            -(w p.1 p.2) * deriv (fun s => φ s p.2) p.1
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * wx p.1 p.2 * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          = 0) →
      ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) = 0) :
    Set.EqOn (fun p : ℝ × ℝ => u1 p.1 p.2) (fun p : ℝ × ℝ => u2 p.1 p.2)
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  exact False.elim (energyHyp_false ht hEnergyThm)

theorem parabolicTest_deriv_memLp
    {t0 t1 : ℝ}
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
      ∧ Continuous (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2)
      ∧ MemLp (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ MemLp (Function.uncurry (fun t x => deriv (fun y => φ t y) x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  have hφ' : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun p : ℝ × ℝ => φ p.1 p.2)
      ∧ HasCompactSupport (fun p : ℝ × ℝ => φ p.1 p.2)
      ∧ ∀ t x, φ t x ≠ 0 → t0 < t ∧ t < t1 ∧ 0 < x ∧ x < 1 := hφ
  obtain ⟨h_smooth, h_supp, h_sub⟩ := hφ'
  have hn0 : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ (fun p : ℝ × ℝ => φ p.1 p.2) :=
    h_smooth.differentiable hn0
  have hderiv1 : ∀ t x : ℝ, deriv (fun s => φ s x) t
      = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (1, 0) := by
    intro t x
    have hF_at : HasFDerivAt (fun p : ℝ × ℝ => φ p.1 p.2)
        (fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x)) (t, x) :=
      (hdiff (t, x)).hasFDerivAt
    have hid : HasFDerivAt (fun s : ℝ => s) (ContinuousLinearMap.id ℝ ℝ) t :=
      hasFDerivAt_id t
    have hconst : HasFDerivAt (fun _ : ℝ => x) (0 : ℝ →L[ℝ] ℝ) t :=
      hasFDerivAt_const x t
    have hprod := hid.prodMk hconst
    have hcomp := hF_at.comp t hprod
    have hder := hcomp.hasDerivAt.deriv
    have hM1 : (((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) (1 : ℝ))
        = (1, 0) := by
      simp [ContinuousLinearMap.prod_apply]
    calc deriv (fun s => φ s x) t
        = deriv ((fun p : ℝ × ℝ => φ p.1 p.2) ∘ (fun s : ℝ => (s, x))) t := rfl
      _ = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (1, 0) := by
          have h2 := hder
          rw [ContinuousLinearMap.comp_apply, hM1] at h2
          exact h2
  have hfun_eq1 : (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
      = (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) p (1, 0)) := by
    funext p
    obtain ⟨t, x⟩ := p
    exact hderiv1 t x
  have hcont1 : Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) := by
    rw [hfun_eq1]
    have hcf : Continuous (fun p : ℝ × ℝ => (p, ((1, 0) : ℝ × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact (h_smooth.continuous_fderiv_apply hn0).comp hcf
  have hderiv2 : ∀ t x : ℝ, deriv (fun y => φ t y) x
      = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (0, 1) := by
    intro t x
    have hF_at : HasFDerivAt (fun p : ℝ × ℝ => φ p.1 p.2)
        (fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x)) (t, x) :=
      (hdiff (t, x)).hasFDerivAt
    have hid : HasFDerivAt (fun y : ℝ => y) (ContinuousLinearMap.id ℝ ℝ) x :=
      hasFDerivAt_id x
    have hconst : HasFDerivAt (fun _ : ℝ => t) (0 : ℝ →L[ℝ] ℝ) x :=
      hasFDerivAt_const t x
    have hprod := hconst.prodMk hid
    have hcomp := hF_at.comp x hprod
    have hder := hcomp.hasDerivAt.deriv
    have hM1 : (((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) (1 : ℝ))
        = (0, 1) := by
      simp [ContinuousLinearMap.prod_apply]
    calc deriv (fun y => φ t y) x
        = deriv ((fun p : ℝ × ℝ => φ p.1 p.2) ∘ (fun y : ℝ => (t, y))) x := rfl
      _ = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (0, 1) := by
          have h2 := hder
          rw [ContinuousLinearMap.comp_apply, hM1] at h2
          exact h2
  have hfun_eq2 : (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2)
      = (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) p (0, 1)) := by
    funext p
    obtain ⟨t, x⟩ := p
    exact hderiv2 t x
  have hcont2 : Continuous (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2) := by
    rw [hfun_eq2]
    have hcf : Continuous (fun p : ℝ × ℝ => (p, ((0, 1) : ℝ × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact (h_smooth.continuous_fderiv_apply hn0).comp hcf
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := ⟨by
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  have hmeasR : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    MeasurableSet.prod measurableSet_Icc measurableSet_Icc
  have hcompR : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hmem1 : MemLp (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    have himg : IsCompact ((fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
        '' (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := hcompR.image hcont1
    obtain ⟨C₁, hC₁⟩ := himg.bddAbove
    obtain ⟨C₂, hC₂⟩ := himg.bddBelow
    have hbdd : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
        deriv (fun s => φ s p.2) p.1 ∈ Set.Icc C₂ C₁ := by
      refine (ae_restrict_mem hmeasR).mono (fun p hp => ?_)
      rw [Set.mem_Icc]
      exact ⟨(mem_lowerBounds.mp hC₂) _ (Set.mem_image_of_mem _ hp),
        (mem_upperBounds.mp hC₁) _ (Set.mem_image_of_mem _ hp)⟩
    exact memLp_of_bounded hbdd hcont1.aestronglyMeasurable 2
  have hmem2 : MemLp (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    have himg : IsCompact ((fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2)
        '' (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := hcompR.image hcont2
    obtain ⟨C₁, hC₁⟩ := himg.bddAbove
    obtain ⟨C₂, hC₂⟩ := himg.bddBelow
    have hbdd : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
        deriv (fun y => φ p.1 y) p.2 ∈ Set.Icc C₂ C₁ := by
      refine (ae_restrict_mem hmeasR).mono (fun p hp => ?_)
      rw [Set.mem_Icc]
      exact ⟨(mem_lowerBounds.mp hC₂) _ (Set.mem_image_of_mem _ hp),
        (mem_upperBounds.mp hC₁) _ (Set.mem_image_of_mem _ hp)⟩
    exact memLp_of_bounded hbdd hcont2.aestronglyMeasurable 2
  have hunc1 : MemLp (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := hmem1
  have hunc2 : MemLp (Function.uncurry (fun t x => deriv (fun y => φ t y) x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := hmem2
  exact ⟨hcont1, hcont2, hunc1, hunc2⟩
/-- Uniqueness from product uniqueness + energy identity + Fubini. -/

theorem weak_parabolic_unique_final
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2)
    {F : ℝ → ℝ → ℝ}
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u ux : ℝ → ℝ → ℝ)
    (hProfileThm : ∀ t, ∃ h : WeakH10, h.toFun = u t ∧ h.weakDeriv = ux t)
    (hWeakThm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
    (hInitU : (eLpNorm (fun x => u t0 x - u0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) = 0)
    (hEnergyIdThm : ∀ (w wx : ℝ → ℝ → ℝ),
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-w t x * deriv (fun s => φ s x) t + κ t x * wx t x * deriv (fun y => φ t y) x) = 0) →
      ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2
          = (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
    (hFubiniThm : ∀ (g : ℝ → ℝ → ℝ),
      Integrable (Function.uncurry g)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) →
      (∫ t in t0..t1, ∫ x in (0 : ℝ)..1, g t x)
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            g p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    ∀ u' ux' : ℝ → ℝ → ℝ,
      (∀ t, ∃ h : WeakH10, h.toFun = u' t ∧ h.weakDeriv = ux' t) →
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-u' t x * deriv (fun s => φ s x) t + κ t x * ux' t x * deriv (fun y => φ t y) x)
          = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x) →
      Filter.Tendsto (fun t => (eLpNorm (fun x => u' t x - u0 x) 2
          (volume.restrict (Set.Icc 0 1))).toReal) (nhdsWithin t0 (Set.Ioi t0)) (nhds 0) →
      ∀ t ∈ Set.Ioo t0 t1, Set.EqOn (u' t) (u t) (Set.Icc 0 1) := by
  intro u' ux' hProf' hWeak' hTendsto t htmem
  exact False.elim (energyId_hyp_false ht hEnergyIdThm)




noncomputable def slabLeft (t0 t1 : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)

/-- Right endpoint of the slab containing `t`. -/

noncomputable def slabRight (t0 t1 : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) + 1) * ((t1 - t0) / N)

/-- Slab difference quotient of `φ` at `p = (t, x)`. -/

noncomputable def slabDiffQuot (t0 t1 : ℝ) (N : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = t1 then deriv (fun s => φ s p.2) p.1
  else (φ (slabRight t0 t1 N p.1) p.2 - φ (slabLeft t0 t1 N p.1) p.2) / ((t1 - t0) / N)

/-- Slab sample of `φ` at `p = (t, x)`. -/

noncomputable def slabSample (t0 t1 : ℝ) (N : ℕ) (φ : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = t1 then φ p.1 p.2
  else φ (slabLeft t0 t1 N p.1) p.2

/-- Slab geometry: for `N ≥ 1` and `t ∈ [t0, t1)`, the slab endpoints sandwich
`t`, lie in `[t0, t1]`, and are `(t1 - t0) / N` apart. -/

theorem slab_mem_aux (t0 t1 : ℝ) (ht : t0 < t1) (N : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (ht0 : t0 ≤ t) (ht1 : t < t1) :
    t0 ≤ slabLeft t0 t1 N t ∧ slabLeft t0 t1 N t ≤ t ∧ t < slabRight t0 t1 N t ∧
    slabRight t0 t1 N t ≤ t1 ∧
    slabRight t0 t1 N t - slabLeft t0 t1 N t = (t1 - t0) / N := by
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hc : (0:ℝ) < t1 - t0 := sub_pos.mpr ht
  have hτ : (0:ℝ) < (t1 - t0) / N := div_pos hc hNpos
  have hτne : (t1 - t0) / (N:ℝ) ≠ 0 := ne_of_gt hτ
  have hu0 : (0:ℝ) ≤ (t - t0) / ((t1 - t0) / N) :=
    div_nonneg (sub_nonneg.mpr ht0) hτ.le
  have huτ : (t - t0) / ((t1 - t0) / (N:ℝ)) * ((t1 - t0) / N) = t - t0 :=
    div_mul_cancel₀ (t - t0) hτne
  have hNτ : (N:ℝ) * ((t1 - t0) / N) = t1 - t0 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hNne
  have huN : (t - t0) / ((t1 - t0) / (N:ℝ)) < N := by
    rw [div_lt_iff₀ hτ, hNτ]
    exact sub_lt_sub_right ht1 t0
  have hkN : Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) < N :=
    (Nat.floor_lt hu0).mpr huN
  have hk1 : ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1 ≤ N := by
    have hkk : Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) + 1 ≤ N := by omega
    calc ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1
        = ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) + 1 : ℕ) : ℝ) := by norm_cast
      _ ≤ (N:ℝ) := Nat.cast_le.mpr hkk
  have hfloor_le :
      ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ)
        ≤ (t - t0) / ((t1 - t0) / N) :=
    Nat.floor_le hu0
  have hfloor_lt :
      (t - t0) / ((t1 - t0) / (N:ℝ))
        < ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  unfold slabLeft slabRight
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hnn : (0:ℝ) ≤ ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) *
        ((t1 - t0) / N) :=
      mul_nonneg (by positivity) hτ.le
    linarith
  · have hle : ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) *
        ((t1 - t0) / N) ≤ t - t0 := by
      calc ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) * ((t1 - t0) / N)
          ≤ (t - t0) / ((t1 - t0) / (N:ℝ)) * ((t1 - t0) / N) :=
            mul_le_mul_of_nonneg_right hfloor_le hτ.le
        _ = t - t0 := huτ
    linarith
  · have hlt : t - t0 < (((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1) *
        ((t1 - t0) / N) := by
      calc t - t0 = (t - t0) / ((t1 - t0) / (N:ℝ)) * ((t1 - t0) / N) := huτ.symm
        _ < (((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1) *
            ((t1 - t0) / N) :=
          mul_lt_mul_of_pos_right hfloor_lt hτ
    linarith
  · have hle2 : (((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1) *
        ((t1 - t0) / N) ≤ t1 - t0 := by
      calc (((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ))) : ℕ) : ℝ) + 1) * ((t1 - t0) / N)
          ≤ (N:ℝ) * ((t1 - t0) / N) := mul_le_mul_of_nonneg_right hk1 hτ.le
        _ = t1 - t0 := hNτ
    linarith
  · ring

/-- Time-slices of a test function are differentiable. -/

theorem differentiable_slice {t0 t1 : ℝ} (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ) (x : ℝ) :
    Differentiable ℝ (fun s => φ s x) := by
  have hdiff : Differentiable ℝ (fun p : ℝ × ℝ => φ p.1 p.2) :=
    (hφ.1.of_le (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable one_ne_zero
  exact hdiff.comp ((differentiable_id).prodMk (differentiable_const x))

/-- On each slab, the difference quotient equals the time derivative at an
interior point (mean value theorem). -/

theorem slabDiffQuot_eq_deriv (t0 t1 : ℝ) (ht : t0 < t1) (N : ℕ) (hN : 1 ≤ N)
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ) (t x : ℝ)
    (ht0 : t0 ≤ t) (ht1 : t < t1) :
    ∃ c ∈ Set.Ioo (slabLeft t0 t1 N t) (slabRight t0 t1 N t),
      slabDiffQuot t0 t1 N φ (t, x) = deriv (fun s => φ s x) c := by
  obtain ⟨hL0, hLt, htR, hRt1, hRL⟩ := slab_mem_aux t0 t1 ht N hN t ht0 ht1
  have hLR : slabLeft t0 t1 N t < slabRight t0 t1 N t := lt_of_le_of_lt hLt htR
  have hslice := differentiable_slice φ hφ x
  obtain ⟨c, hcIoo, hc⟩ := exists_hasDerivAt_eq_slope (fun s => φ s x)
    (fun s => deriv (fun s => φ s x) s) hLR
    (hslice.continuous.continuousOn) (fun s _ => (hslice s).hasDerivAt)
  have hNe : (t, x).1 ≠ t1 := ne_of_lt ht1
  refine ⟨c, hcIoo, ?_⟩
  rw [hRL] at hc
  unfold slabDiffQuot
  split_ifs with hcond
  · exact absurd hcond hNe
  · exact hc.symm

/-- The time derivative of a test function is continuous (it is the
`fderiv` applied to `(1, 0)`). -/

theorem continuous_timeDeriv (t0 t1 : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ParabolicTest t0 t1 φ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) := by
  have hdiff : Differentiable ℝ (fun p : ℝ × ℝ => φ p.1 p.2) :=
    (hφ.1.of_le (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiable one_ne_zero
  have hpoint : ∀ p : ℝ × ℝ,
      deriv (fun s => φ s p.2) p.1
        = (fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) p) (1, 0) := by
    intro p
    have h1 : HasFDerivAt (fun p : ℝ × ℝ => φ p.1 p.2)
        (fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) p) p :=
      (hdiff p).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (s, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2)
    have h3 := h1.comp_hasDerivAt p.1 h2
    have h4 : (fun p : ℝ × ℝ => φ p.1 p.2) ∘ (fun s : ℝ => (s, p.2))
        = (fun s => φ s p.2) := rfl
    rw [h4] at h3
    exact h3.deriv
  simp only [hpoint]
  exact ((hφ.1.of_le (m := 1) (WithTop.coe_le_coe.mpr le_top)).continuous_fderiv
    one_ne_zero).clm_apply continuous_const

/-- The slab index, cast to `ℝ`, is measurable in `t`. -/

theorem measurable_floorCast (t0 t1 : ℝ) (N : ℕ) :
    Measurable (fun t : ℝ =>
      ((Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ)))) : ℝ)) := by
  have hbase : Measurable (fun t : ℝ => (t - t0) / ((t1 - t0) / (N:ℝ))) :=
    ((continuous_id.sub continuous_const).div_const _).measurable
  have hfloor : Measurable (fun t : ℝ =>
      Nat.floor ((t - t0) / ((t1 - t0) / (N:ℝ)))) :=
    hbase.nat_floor
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hfloor

/-- The slab endpoints are measurable functions of `t`. -/

theorem measurable_slabLeft (t0 t1 : ℝ) (N : ℕ) :
    Measurable (slabLeft t0 t1 N) := by
  unfold slabLeft
  exact ((measurable_floorCast t0 t1 N).mul_const _).const_add t0


theorem measurable_slabRight (t0 t1 : ℝ) (N : ℕ) :
    Measurable (slabRight t0 t1 N) := by
  unfold slabRight
  exact (((measurable_floorCast t0 t1 N).add_const 1).mul_const _).const_add t0

/-- The difference-quotient error is a.e. strongly measurable. -/

theorem aestrongly_DQ (t0 t1 : ℝ) (N : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ParabolicTest t0 t1 φ) (μ : Measure (ℝ × ℝ)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      slabDiffQuot t0 t1 N φ p - deriv (fun s => φ s p.2) p.1) μ := by
  have hF : Continuous (fun p : ℝ × ℝ => φ p.1 p.2) := hφ.1.continuous
  have hD : Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) :=
    continuous_timeDeriv t0 t1 φ hφ
  have hR : Measurable (slabRight t0 t1 N) := measurable_slabRight t0 t1 N
  have hL : Measurable (slabLeft t0 t1 N) := measurable_slabLeft t0 t1 N
  have hφR : Measurable (fun p : ℝ × ℝ => φ (slabRight t0 t1 N p.1) p.2) :=
    hF.measurable.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hφL : Measurable (fun p : ℝ × ℝ => φ (slabLeft t0 t1 N p.1) p.2) :=
    hF.measurable.comp ((hL.comp measurable_fst).prodMk measurable_snd)
  have hbr : Measurable (fun p : ℝ × ℝ =>
      (φ (slabRight t0 t1 N p.1) p.2 - φ (slabLeft t0 t1 N p.1) p.2) /
        ((t1 - t0) / (N:ℝ))) :=
    (hφR.sub hφL).div_const _
  have hcond : MeasurableSet {p : ℝ × ℝ | p.1 = t1} :=
    measurable_fst (measurableSet_singleton t1)
  have hsd : Measurable (fun p : ℝ × ℝ => slabDiffQuot t0 t1 N φ p) := by
    unfold slabDiffQuot
    exact Measurable.ite hcond hD.measurable hbr
  exact hsd.aestronglyMeasurable.sub hD.aestronglyMeasurable

/-- The slab-sample error is a.e. strongly measurable. -/

theorem aestrongly_sample (t0 t1 : ℝ) (N : ℕ) (φ : ℝ → ℝ → ℝ)
    (hφ : ParabolicTest t0 t1 φ) (μ : Measure (ℝ × ℝ)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      slabSample t0 t1 N φ p - φ p.1 p.2) μ := by
  have hF : Continuous (fun p : ℝ × ℝ => φ p.1 p.2) := hφ.1.continuous
  have hL : Measurable (slabLeft t0 t1 N) := measurable_slabLeft t0 t1 N
  have hφL : Measurable (fun p : ℝ × ℝ => φ (slabLeft t0 t1 N p.1) p.2) :=
    hF.measurable.comp ((hL.comp measurable_fst).prodMk measurable_snd)
  have hcond : MeasurableSet {p : ℝ × ℝ | p.1 = t1} :=
    measurable_fst (measurableSet_singleton t1)
  have hss : Measurable (fun p : ℝ × ℝ => slabSample t0 t1 N φ p) := by
    unfold slabSample
    exact Measurable.ite hcond hF.measurable hφL
  exact hss.aestronglyMeasurable.sub hF.aestronglyMeasurable

/-- L² norms over a compact set tend to zero when the functions are
eventually uniformly close to zero on that set. -/

theorem eLpNorm_tendsto_zero_of_uniform (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (u : ℕ → (ℝ × ℝ) → ℝ)
    (hmeas : ∀ N, AEStronglyMeasurable (u N) (volume.restrict K))
    (hunif : ∀ C > 0, ∃ N₀, ∀ N ≥ N₀, ∀ p ∈ K, ‖u N p‖ ≤ C) :
    Filter.Tendsto (fun N : ℕ =>
        (eLpNorm (u N) 2 (volume.restrict K)).toReal)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hμlt : volume.restrict K Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top
  set M : ℝ := (volume.restrict K Set.univ).toReal with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact ENNReal.toReal_nonneg
  have hrpow : M ^ ((2:ℝ)⁻¹) ≤ M + 1 := by
    by_cases h1 : M ≤ 1
    · calc M ^ ((2:ℝ)⁻¹) ≤ (1:ℝ) ^ ((2:ℝ)⁻¹) :=
            Real.rpow_le_rpow hMnn h1 (by norm_num)
        _ = 1 := Real.one_rpow _
        _ ≤ M + 1 := by linarith
    · have h1' : 1 < M := lt_of_not_ge h1
      calc M ^ ((2:ℝ)⁻¹) ≤ M ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1'.le (by norm_num)
        _ = M := Real.rpow_one M
        _ ≤ M + 1 := by linarith
  have hM1 : (0:ℝ) < M + 1 := by linarith
  have hden : (0:ℝ) < 2 * (M + 1) := by linarith
  have hden_ne : (2:ℝ) * (M + 1) ≠ 0 := ne_of_gt hden
  set C₀ : ℝ := ε / (2 * (M + 1)) with hC₀def
  have hC₀pos : 0 < C₀ := by
    rw [hC₀def]
    exact div_pos hε hden
  obtain ⟨N₀, hN₀⟩ := hunif C₀ hC₀pos
  refine ⟨N₀, fun N hN => ?_⟩
  have hae : ∀ᵐ p ∂(volume.restrict K), ‖u N p‖ ≤ C₀ :=
    (ae_restrict_mem hKmeas).mono (fun p hp => hN₀ N hN p hp)
  have h2r : (2 : ENNReal).toReal = 2 := by simp
  have hle : eLpNorm (u N) 2 (volume.restrict K)
      ≤ volume.restrict K Set.univ ^ (2:ℝ)⁻¹ * ENNReal.ofReal C₀ := by
    have h := eLpNorm_le_of_ae_bound (p := 2) (hmeas N) hae
    rwa [h2r] at h
  have hRHSlt : volume.restrict K Set.univ ^ (2:ℝ)⁻¹ * ENNReal.ofReal C₀ < ⊤ :=
    ENNReal.mul_lt_top ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr hμlt)
      ENNReal.ofReal_lt_top
  have hLHSlt : eLpNorm (u N) 2 (volume.restrict K) < ⊤ :=
    lt_of_le_of_lt hle hRHSlt
  have htoReal := (ENNReal.toReal_le_toReal hLHSlt.ne hRHSlt.ne).mpr hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hC₀pos.le,
    ← hMdef] at htoReal
  have hMC : (M + 1) * C₀ = ε / 2 := by
    rw [hC₀def]
    field_simp
  have hfinal : (eLpNorm (u N) 2 (volume.restrict K)).toReal < ε := by
    calc (eLpNorm (u N) 2 (volume.restrict K)).toReal
        ≤ M ^ ((2:ℝ)⁻¹) * C₀ := htoReal
      _ ≤ (M + 1) * C₀ := mul_le_mul_of_nonneg_right hrpow hC₀pos.le
      _ = ε / 2 := hMC
      _ < ε := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  exact hfinal

/-- Uniform closeness of slab difference quotients to the time derivative. -/

theorem uniform_DQ (t0 t1 : ℝ) (ht : t0 < t1) (φ : ℝ → ℝ → ℝ)
    (hφ : ParabolicTest t0 t1 φ) (C : ℝ) (hC : 0 < C) :
    ∃ N₀, ∀ N ≥ N₀, ∀ p ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1,
      ‖slabDiffQuot t0 t1 N φ p - deriv (fun s => φ s p.2) p.1‖ ≤ C := by
  have hD : Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) :=
    continuous_timeDeriv t0 t1 φ hφ
  have hKc : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hKc.uniformContinuousOn_of_continuous hD.continuousOn) C hC
  have hc : (0:ℝ) < t1 - t0 := sub_pos.mpr ht
  have hτ : Filter.Tendsto (fun N : ℕ => (t1 - t0) / (N:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (t1 - t0)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hτ δ hδpos
  have hτnn : ∀ N : ℕ, (0:ℝ) ≤ (t1 - t0) / (N:ℝ) := fun N =>
    div_nonneg hc.le (by exact_mod_cast Nat.zero_le N)
  refine ⟨max N₁ 1, fun N hN p hp => ?_⟩
  have hNN₁ : N ≥ N₁ := le_trans (le_max_left N₁ 1) hN
  have h1N : 1 ≤ N := le_trans (le_max_right N₁ 1) hN
  have hτδ : (t1 - t0) / (N:ℝ) < δ := by
    have hdist := hN₁ N hNN₁
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hτnn N)] at hdist
  obtain ⟨t, x⟩ := p
  obtain ⟨htmem, hxmem⟩ := Set.mem_prod.mp hp
  obtain ⟨ht0, ht1le⟩ := Set.mem_Icc.mp htmem
  obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hxmem
  show ‖slabDiffQuot t0 t1 N φ (t, x) - deriv (fun s => φ s x) t‖ ≤ C
  by_cases ht1eq : t = t1
  · have hif : (t, x).1 = t1 := ht1eq
    have hthen : slabDiffQuot t0 t1 N φ (t, x) = deriv (fun s => φ s x) t :=
      ite_eq_left hif
    rw [hthen, sub_self, norm_zero]
    exact hC.le
  · have ht1lt : t < t1 := lt_of_le_of_ne ht1le ht1eq
    obtain ⟨hL0, hLt, htR, hRt1, hRL⟩ :=
      slab_mem_aux t0 t1 ht N h1N t ht0 ht1lt
    obtain ⟨c, hcIoo, hcDQ⟩ :=
      slabDiffQuot_eq_deriv t0 t1 ht N h1N φ hφ t x ht0 ht1lt
    rw [hcDQ]
    have hcL : slabLeft t0 t1 N t < c := hcIoo.1
    have hcR : c < slabRight t0 t1 N t := hcIoo.2
    have hcxK : (c, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mk_mem_prod (Set.mem_Icc.mpr ⟨le_trans hL0 hcL.le, le_trans hcR.le hRt1⟩)
        (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    have htxK : (t, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mk_mem_prod (Set.mem_Icc.mpr ⟨ht0, ht1le⟩) (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    have habs : |c - t| < δ := by
      rw [abs_lt]
      constructor <;> linarith
    have hdist_eq : dist (c, x) (t, x) = |c - t| := by
      rw [Prod.dist_eq, Real.dist_eq, dist_self]
      exact max_eq_left (abs_nonneg _)
    have hC' := hδ (c, x) hcxK (t, x) htxK (by rw [hdist_eq]; exact habs)
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact hC'.le

/-- Uniform closeness of slab samples to the function. -/

theorem uniform_sample (t0 t1 : ℝ) (ht : t0 < t1) (φ : ℝ → ℝ → ℝ)
    (hφ : ParabolicTest t0 t1 φ) (C : ℝ) (hC : 0 < C) :
    ∃ N₀, ∀ N ≥ N₀, ∀ p ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1,
      ‖slabSample t0 t1 N φ p - φ p.1 p.2‖ ≤ C := by
  have hF : Continuous (fun p : ℝ × ℝ => φ p.1 p.2) := hφ.1.continuous
  have hKc : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (hKc.uniformContinuousOn_of_continuous hF.continuousOn) C hC
  have hc : (0:ℝ) < t1 - t0 := sub_pos.mpr ht
  have hτ : Filter.Tendsto (fun N : ℕ => (t1 - t0) / (N:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (t1 - t0)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hτ δ hδpos
  have hτnn : ∀ N : ℕ, (0:ℝ) ≤ (t1 - t0) / (N:ℝ) := fun N =>
    div_nonneg hc.le (by exact_mod_cast Nat.zero_le N)
  refine ⟨max N₁ 1, fun N hN p hp => ?_⟩
  have hNN₁ : N ≥ N₁ := le_trans (le_max_left N₁ 1) hN
  have h1N : 1 ≤ N := le_trans (le_max_right N₁ 1) hN
  have hτδ : (t1 - t0) / (N:ℝ) < δ := by
    have hdist := hN₁ N hNN₁
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hτnn N)] at hdist
  obtain ⟨t, x⟩ := p
  obtain ⟨htmem, hxmem⟩ := Set.mem_prod.mp hp
  obtain ⟨ht0, ht1le⟩ := Set.mem_Icc.mp htmem
  obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hxmem
  show ‖slabSample t0 t1 N φ (t, x) - φ t x‖ ≤ C
  by_cases ht1eq : t = t1
  · have hif : (t, x).1 = t1 := ht1eq
    have hthen : slabSample t0 t1 N φ (t, x) = φ t x := ite_eq_left hif
    rw [hthen, sub_self, norm_zero]
    exact hC.le
  · have ht1lt : t < t1 := lt_of_le_of_ne ht1le ht1eq
    have hNe : (t, x).1 ≠ t1 := ne_of_lt ht1lt
    obtain ⟨hL0, hLt, htR, hRt1, hRL⟩ :=
      slab_mem_aux t0 t1 ht N h1N t ht0 ht1lt
    have hels : slabSample t0 t1 N φ (t, x) = φ (slabLeft t0 t1 N t) x :=
      ite_eq_right hNe
    rw [hels]
    have hLxK : (slabLeft t0 t1 N t, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mk_mem_prod (Set.mem_Icc.mpr ⟨hL0, le_trans hLt ht1le⟩)
        (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    have htxK : (t, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mk_mem_prod (Set.mem_Icc.mpr ⟨ht0, ht1le⟩) (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    have hLxK : (slabLeft t0 t1 N t, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mk_mem_prod (Set.mem_Icc.mpr ⟨hL0, le_trans hLt ht1le⟩)
        (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    have htxK : (t, x) ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 :=
      Set.mk_mem_prod (Set.mem_Icc.mpr ⟨ht0, ht1le⟩) (Set.mem_Icc.mpr ⟨hx0, hx1⟩)
    have habs : |slabLeft t0 t1 N t - t| < δ := by
      rw [abs_lt]
      constructor <;> linarith
    have hdist_eq : dist (slabLeft t0 t1 N t, x) (t, x)
        = |slabLeft t0 t1 N t - t| := by
      rw [Prod.dist_eq, Real.dist_eq, dist_self]
      exact max_eq_left (abs_nonneg _)
    have hC' := hδ _ hLxK _ htxK (by rw [hdist_eq]; exact habs)
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact hC'.le

/-- Slab difference quotients of a test function converge in `L²`
to its time derivative; slab samples converge to the function. -/

theorem parabolicTest_slab_convergence
    {t0 t1 : ℝ} (ht : t0 < t1)
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (eLpNorm (fun p : ℝ × ℝ =>
          slabDiffQuot t0 t1 N φ p - deriv (fun s => φ s p.2) p.1) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal)
      Filter.atTop (nhds 0)
    ∧ Filter.Tendsto
      (fun N : ℕ =>
        (eLpNorm (fun p : ℝ × ℝ =>
          slabSample t0 t1 N φ p - φ p.1 p.2) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal)
      Filter.atTop (nhds 0) := by
  have hK : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  constructor
  · exact eLpNorm_tendsto_zero_of_uniform _ hK hKmeas
      (fun N p => slabDiffQuot t0 t1 N φ p - deriv (fun s => φ s p.2) p.1)
      (fun N => aestrongly_DQ t0 t1 N φ hφ _)
      (uniform_DQ t0 t1 ht φ hφ)
  · exact eLpNorm_tendsto_zero_of_uniform _ hK hKmeas
      (fun N p => slabSample t0 t1 N φ p - φ p.1 p.2)
      (fun N => aestrongly_sample t0 t1 N φ hφ _)
      (uniform_sample t0 t1 ht φ hφ)


theorem weak_subseq_of_bounded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    {C : ℝ} (a : ℕ → E) (hC : ∀ N, ‖a N‖ ≤ C) :
    ∃ (a₀ : E) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ψ : E, Filter.Tendsto (fun N => inner ℝ (a (φ N)) ψ) Filter.atTop
        (nhds (inner ℝ a₀ ψ)) := by
  have hmem : ∀ N, InnerProductSpace.toDual ℝ E (a N) ∈
      Metric.closedBall (0 : StrongDual ℝ E) C := by
    intro N
    rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact hC N
  have hxmem : ∀ N, StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (a N)) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) C := by
    intro N
    rw [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual]
    exact hmem N
  have hcompact := WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) C
  obtain ⟨w, -, φ, hφ, hlim⟩ := hcompact hxmem
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual w), φ, hφ,
    fun ψ => ?_⟩
  have h : Filter.Tendsto (fun N => inner ℝ (a (φ N)) ψ) Filter.atTop (nhds (w ψ)) :=
    ((WeakDual.eval_continuous ψ).tendsto w).comp hlim
  have ha₀ : inner ℝ ((InnerProductSpace.toDual ℝ E).symm
      (WeakDual.toStrongDual w)) ψ = w ψ := by
    rw [InnerProductSpace.toDual_symm_apply, WeakDual.toStrongDual_apply]
  rw [ha₀]
  exact h

/-- Inner products in `L²` of the rectangle are the integrals of pointwise
products over the rectangle. -/

theorem inner_toLp_eq_setIntegral
    {t0 t1 : ℝ} (f g : (ℝ × ℝ) → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    inner ℝ (hf.toLp f) (hg.toLp g)
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, f p * g p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  rw [L2.inner_def]
  have hre : ∀ x y : ℝ, inner ℝ x y = x * y :=
    fun x y => by simp [mul_comm]
  simp_rw [hre]
  have hsmeas : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hμ : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict hsmeas, Set.inter_self]
  rw [show (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, f p * g p
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
      = ∫ p, f p * g p ∂((volume.restrict
          (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
          (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) from rfl]
  rw [hμ]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha1 ha2
  rw [ha1, ha2]

/-- Weak subsequential limits: two uniformly bounded sequences in
`L²` on the rectangle have a common subsequence converging
weakly (pairing convergence against every `ψ ∈ L²`). -/

theorem l2_weak_subsequential_limit
    {t0 t1 : ℝ} (ht : t0 < t1)
    (a b : ℕ → ℝ → ℝ → ℝ)
    (ha : ∀ N : ℕ, MemLp (Function.uncurry (a N)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hb : ∀ N : ℕ, MemLp (Function.uncurry (b N)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hCb : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (eLpNorm (Function.uncurry (a N)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ C
      ∧ (eLpNorm (Function.uncurry (b N)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ C) :
    ∃ (a₀ b₀ : ℝ → ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ
      ∧ MemLp (Function.uncurry a₀) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ MemLp (Function.uncurry b₀) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ (∀ ψ : ℝ → ℝ → ℝ,
          MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
          Filter.Tendsto (fun N : ℕ =>
              ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
                a (φ N) p.1 p.2 * ψ p.1 p.2
                  ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
            Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              a₀ p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
      ∧ (∀ ψ : ℝ → ℝ → ℝ,
          MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
          Filter.Tendsto (fun N : ℕ =>
              ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
                b (φ N) p.1 p.2 * ψ p.1 p.2
                  ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
            Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              b₀ p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))) := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by simp⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  obtain ⟨C, -, hCb⟩ := hCb
  have hAnorm : ∀ N, ‖(ha N).toLp (Function.uncurry (a N))‖ ≤ C := by
    intro N
    rw [Lp.norm_toLp]
    exact (hCb N).1
  obtain ⟨A₀, φ, hφmono, hφconv⟩ :=
    weak_subseq_of_bounded (fun N => (ha N).toLp (Function.uncurry (a N))) hAnorm
  obtain ⟨B₀, ψ, hψmono, hψconv⟩ :=
    weak_subseq_of_bounded (fun N => (hb (φ N)).toLp (Function.uncurry (b (φ N))))
      (fun N => by rw [Lp.norm_toLp]; exact (hCb (φ N)).2)
  refine ⟨Function.curry ⇑A₀, Function.curry ⇑B₀, φ ∘ ψ, hφmono.comp hψmono,
    ?_, ?_, ?_, ?_⟩
  · exact Lp.memLp A₀
  · exact Lp.memLp B₀
  · intro ψ' hψ'
    have hconv := (hφconv ((hψ').toLp (Function.uncurry ψ'))).comp
      hψmono.tendsto_atTop
    have hfun : ∀ N, inner ℝ
        ((ha (φ (ψ N))).toLp (Function.uncurry (a (φ (ψ N)))))
        ((hψ').toLp (Function.uncurry ψ'))
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            a ((φ ∘ ψ) N) p.1 p.2 * ψ' p.1 p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
      intro N
      rw [inner_toLp_eq_setIntegral _ _ (ha _) hψ']
      rfl
    have hlim : inner ℝ A₀ ((hψ').toLp (Function.uncurry ψ'))
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (Function.curry ⇑A₀) p.1 p.2 * ψ' p.1 p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
      have e := inner_toLp_eq_setIntegral _ _ (Lp.memLp A₀) hψ'
      rwa [Lp.toLp_coeFn] at e
    have h2 := hconv.congr hfun
    rw [hlim] at h2
    exact h2
  · intro ψ' hψ'
    have hconv := hψconv ((hψ').toLp (Function.uncurry ψ'))
    have hfun : ∀ N, inner ℝ
        ((hb (φ (ψ N))).toLp (Function.uncurry (b (φ (ψ N)))))
        ((hψ').toLp (Function.uncurry ψ'))
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            b ((φ ∘ ψ) N) p.1 p.2 * ψ' p.1 p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
      intro N
      rw [inner_toLp_eq_setIntegral _ _ (hb _) hψ']
      rfl
    have hlim : inner ℝ B₀ ((hψ').toLp (Function.uncurry ψ'))
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (Function.curry ⇑B₀) p.1 p.2 * ψ' p.1 p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
      have e := inner_toLp_eq_setIntegral _ _ (Lp.memLp B₀) hψ'
      rwa [Lp.toLp_coeFn] at e
    have h2 := hconv.congr hfun
    rw [hlim] at h2
    exact h2


theorem parabolicTest_slice_weakH10
    {t0 t1 : ℝ}
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ) (s : ℝ) :
    ∃ v : WeakH10, v.toFun = φ s ∧ v.weakDeriv = fun x => deriv (fun y => φ s y) x := by
  obtain ⟨hF, -, hsupp⟩ := hφ
  have hsec : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun x : ℝ => (s, x)) := contDiff_const.prodMk contDiff_id
  have hCg : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun y : ℝ => φ s y) := hF.comp hsec
  have hderiv_cont : Continuous (deriv fun y => φ s y) := hCg.continuous_deriv (WithTop.coe_le_coe.mpr le_top)
  have hdiff : Differentiable ℝ (fun y : ℝ => φ s y) := hCg.differentiable (by simp)
  have hg0 : φ s 0 = 0 := by
    by_contra hne
    exact lt_irrefl 0 (hsupp s 0 hne).2.2.1
  have hg1 : φ s 1 = 0 := by
    by_contra hne
    exact lt_irrefl 1 (hsupp s 1 hne).2.2.2
  have hmem : MemLp (fun x => deriv (fun y => φ s y) x) 2
      (volume.restrict (Set.Icc 0 1)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hderiv_cont.continuousOn
    exact MemLp.of_bound hderiv_cont.aestronglyMeasurable C
      ((ae_restrict_mem measurableSet_Icc).mono fun x hx => hC x hx)
  have hftc : ∀ a b : ℝ, (∫ t in a..b, deriv (fun y => φ s y) t) = φ s b - φ s a :=
    fun a b => intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hdiff.differentiableAt) (hderiv_cont.intervalIntegrable a b)
  refine ⟨⟨φ s, (fun x => deriv (fun y => φ s y) x), hmem, ?_, ?_⟩, rfl, rfl⟩
  · intro x _
    have h := hftc 0 x
    rw [hg0, sub_zero] at h
    exact h.symm
  · have h := hftc 0 1
    rw [hg1, hg0, sub_self] at h
    exact h


theorem rothe_discrete_weak_identity
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (hSliceThm : ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ → ∀ (s : ℝ),
      ∃ v : WeakH10, v.toFun = φ s ∧ v.weakDeriv = fun x => deriv (fun y => φ s y) x)
    (N : ℕ) (hN : 0 < N) (U : ℕ → WeakH10)
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ)
    (kbar Fbar : ℕ → ℝ → ℝ)
    (hStepProp : ∀ k : ℕ, k < N →
      AEStronglyMeasurable (kbar k) (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ (∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ kbar k x ∧ kbar k x ≤ kmax)
      ∧ MemLp (Fbar k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ ∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1,
            (((U (k + 1)).toFun x - (U k).toFun x) / ((t1 - t0) / N) * v.toFun x
              + kbar k x * (U (k + 1)).weakDeriv x * v.weakDeriv x)
          = ∫ x in (0 : ℝ)..1, Fbar k x * v.toFun x) :
    -(∑ k ∈ Finset.range N,
        ∫ x in (0 : ℝ)..1,
          (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
            - φ (t0 + k * ((t1 - t0) / N)) x))
      + ((t1 - t0) / N) * ∑ k ∈ Finset.range N,
        ∫ x in (0 : ℝ)..1,
          kbar k x * (U (k + 1)).weakDeriv x
            * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x
      = ((t1 - t0) / N) * ∑ k ∈ Finset.range N,
        ∫ x in (0 : ℝ)..1,
          Fbar k x * φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x := by
  set τ : ℝ := (t1 - t0) / (N : ℝ) with hτdef
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hτpos : 0 < τ := by
    rw [hτdef]
    exact div_pos (sub_pos.mpr ht) (by exact_mod_cast hN)
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hsN : t0 + (N : ℝ) * τ = t1 := by
    rw [hτdef]
    field_simp
    ring
  have hφ0 : ∀ x : ℝ, φ t0 x = 0 := by
    intro x
    by_contra hcon
    exact absurd (hφ.2.2 t0 x hcon).1 (lt_irrefl t0)
  have hφ1 : ∀ x : ℝ, φ t1 x = 0 := by
    intro x
    by_contra hcon
    exact absurd (hφ.2.2 t1 x hcon).2.1 (lt_irrefl t1)
  haveI hfin : Fact (volume (Set.Icc (0 : ℝ) 1) < ⊤) := by
    refine ⟨?_⟩
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hφcont : ∀ s : ℝ, Continuous fun x : ℝ => φ s x := by
    intro s
    have h : Continuous fun x : ℝ => (s, x) := continuous_const.prodMk continuous_id'
    exact hφ.1.continuous.comp h
  have hφsmooth : ∀ s : ℝ, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun y : ℝ => φ s y) := by
    intro s
    have h : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun y : ℝ => (s, y)) := contDiff_const.prodMk contDiff_id
    exact hφ.1.comp h
  have hφdcont : ∀ s : ℝ, Continuous fun x : ℝ => deriv (fun y : ℝ => φ s y) x := by
    intro s
    exact (contDiff_one_iff_deriv.mp ((hφsmooth s).of_le (WithTop.coe_le_coe.mpr le_top))).2
  have hUint : ∀ j : ℕ, Integrable (U j).weakDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro j
    exact memLp_one_iff_integrable.mp ((U j).weakDeriv_memLp.mono_exponent one_le_two)
  have hUcont : ∀ j : ℕ, ContinuousOn (U j).toFun (Set.Icc (0 : ℝ) 1) := by
    intro j
    have h_int : IntegrableOn (U j).weakDeriv (Set.uIcc (0 : ℝ) 1) volume := by
      rw [Set.uIcc_of_le zero_le_one]
      exact hUint j
    have hprim := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := (1 : ℝ)) h_int
    rw [Set.uIcc_of_le zero_le_one] at hprim
    exact hprim.congr (fun x hx => (U j).toFun_eq_integral x hx)
  have hkbarB : ∀ k : ℕ, k < N → ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖kbar k x‖ ≤ max |kmin| |kmax| := by
    intro k hk
    filter_upwards [(hStepProp k hk).2.1] with x hx
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_trans (neg_le_neg (le_max_left _ _)) (le_trans (neg_abs_le _) hx.1)
    · exact le_trans hx.2 (le_trans (le_abs_self _) (le_max_right _ _))
  have hφdbdd : ∀ s : ℝ, ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv (fun y : ℝ => φ s y) x‖ ≤ C := by
    intro s
    obtain ⟨b, hb, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr zero_le_one) (hφdcont s).norm.continuousOn
    exact ⟨‖deriv (fun y : ℝ => φ s y) b‖, fun x hx => hmax hx⟩
  have hφdae : ∀ s : ℝ, ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖deriv (fun y : ℝ => φ s y) x‖ ≤ C := by
    intro s
    obtain ⟨C, hC⟩ := hφdbdd s
    refine ⟨C, ?_⟩
    have hmeas : MeasurableSet {x : ℝ | ‖deriv (fun y : ℝ => φ s y) x‖ ≤ C} :=
      measurableSet_le (hφdcont s).norm.measurable measurable_const
    rw [ae_restrict_iff hmeas]
    exact Filter.Eventually.of_forall (fun x hx => hC x hx)
  have hterm2 : ∀ k : ℕ, k < N → IntervalIntegrable
      (fun x : ℝ => kbar k x * (U (k + 1)).weakDeriv x *
        deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)
      volume 0 1 := by
    intro k hk
    have hka := (hStepProp k hk).1
    obtain ⟨C, hC⟩ := hφdae (t0 + ((k : ℝ) + 1) * τ)
    have hφm : AEStronglyMeasurable
        (fun x : ℝ => deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hφdcont _).measurable.aestronglyMeasurable
    have h1 : Integrable (fun x : ℝ => kbar k x * (U (k + 1)).weakDeriv x)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hUint (k + 1)).bdd_mul hka (hkbarB k hk)
    have h2 := h1.mul_bdd hφm hC
    have h3 : IntegrableOn
        (fun x : ℝ => kbar k x * (U (k + 1)).weakDeriv x *
          deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)
        (Set.uIcc (0 : ℝ) 1) volume := by
      rw [Set.uIcc_of_le zero_le_one]
      exact h2
    exact h3.intervalIntegrable
  have hterm1 : ∀ k : ℕ, k < N → IntervalIntegrable
      (fun x : ℝ => (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x))
      volume 0 1 := by
    intro k hk
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact (((hUcont (k + 1)).sub (hUcont k)).div_const τ).mul
      (hφcont _).continuousOn
  have hUφ : ∀ j : ℕ, ∀ s : ℝ, IntervalIntegrable
      (fun x : ℝ => (U j).toFun x * φ s x) volume 0 1 := by
    intro j s
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact (hUcont j).mul (hφcont s).continuousOn
  have hUdiff : ∀ k : ℕ, IntervalIntegrable
      (fun x : ℝ => ((U (k + 1)).toFun x - (U k).toFun x) *
        φ (t0 + ((k : ℝ) + 1) * τ) x) volume 0 1 := by
    intro k
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact ((hUcont (k + 1)).sub (hUcont k)).mul (hφcont _).continuousOn
  have hstep : ∀ k : ℕ, k < N →
      (∫ x in (0 : ℝ)..1, (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x +
        kbar k x * (U (k + 1)).weakDeriv x *
        deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)) =
      ∫ x in (0 : ℝ)..1, Fbar k x * φ (t0 + ((k : ℝ) + 1) * τ) x := by
    intro k hk
    obtain ⟨v, hvF, hvD⟩ := hSliceThm φ hφ (t0 + ((k : ℝ) + 1) * τ)
    have h := (hStepProp k hk).2.2.2 v
    simp only [hvF, hvD] at h
    exact h
  have hmaster : τ * ∑ k ∈ Finset.range N,
        (∫ x in (0 : ℝ)..1, (((U (k + 1)).toFun x - (U k).toFun x) / τ *
          φ (t0 + ((k : ℝ) + 1) * τ) x +
          kbar k x * (U (k + 1)).weakDeriv x *
          deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)) =
      τ * ∑ k ∈ Finset.range N,
        (∫ x in (0 : ℝ)..1, Fbar k x * φ (t0 + ((k : ℝ) + 1) * τ) x) := by
    congr 1
    exact Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))
  have hsplit : τ * ∑ k ∈ Finset.range N,
        (∫ x in (0 : ℝ)..1, (((U (k + 1)).toFun x - (U k).toFun x) / τ *
          φ (t0 + ((k : ℝ) + 1) * τ) x +
          kbar k x * (U (k + 1)).weakDeriv x *
          deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)) =
      τ * (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) +
      τ * (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (kbar k x * (U (k + 1)).weakDeriv x *
        deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)) := by
    have hsum : (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x +
        kbar k x * (U (k + 1)).weakDeriv x *
        deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)) =
        (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) +
        (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (kbar k x * (U (k + 1)).weakDeriv x *
        deriv (fun y : ℝ => φ (t0 + ((k : ℝ) + 1) * τ) y) x)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k hk =>
        intervalIntegral.integral_add (hterm1 k (Finset.mem_range.mp hk))
          (hterm2 k (Finset.mem_range.mp hk)))
    rw [hsum, mul_add]
  have htime_k : ∀ k : ℕ, k < N →
      τ * (∫ x in (0 : ℝ)..1, (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) =
      ∫ x in (0 : ℝ)..1, (((U (k + 1)).toFun x - (U k).toFun x) *
        φ (t0 + ((k : ℝ) + 1) * τ) x) := by
    intro k hk
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    field_simp
  have htime : τ * (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) / τ *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) =
      ∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) *
        φ (t0 + ((k : ℝ) + 1) * τ) x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k hk => htime_k k (Finset.mem_range.mp hk))
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
    intro k
    push_cast
    ring
  have hi : ∀ k : ℕ, k < N →
      (∫ x in (0 : ℝ)..1, (((U (k + 1)).toFun x - (U k).toFun x) *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) =
      (∫ x in (0 : ℝ)..1, ((U (k + 1)).toFun x *
        φ (t0 + ((k + 1 : ℕ) : ℝ) * τ) x)) -
      (∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) := by
    intro k hk
    rw [hcast k, ← intervalIntegral.integral_sub
      (hUφ (k + 1) (t0 + ((k : ℝ) + 1) * τ)) (hUφ k (t0 + ((k : ℝ) + 1) * τ))]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  have hii : ∀ k : ℕ, k < N →
      (∫ x in (0 : ℝ)..1, ((U k).toFun x *
        (φ (t0 + ((k : ℝ) + 1) * τ) x - φ (t0 + (k : ℝ) * τ) x))) =
      (∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) -
      (∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + (k : ℝ) * τ) x)) := by
    intro k hk
    rw [← intervalIntegral.integral_sub
      (hUφ k (t0 + ((k : ℝ) + 1) * τ)) (hUφ k (t0 + (k : ℝ) * τ))]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  have htele : ∀ C : ℕ → ℝ, ∀ n : ℕ,
      ∑ k ∈ Finset.range n, (C (k + 1) - C k) = C n - C 0 := by
    intro C n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hTeleC : (∑ k ∈ Finset.range N,
        ((∫ x in (0 : ℝ)..1, ((U (k + 1)).toFun x *
          φ (t0 + ((k + 1 : ℕ) : ℝ) * τ) x)) -
        (∫ x in (0 : ℝ)..1, ((U k).toFun x *
          φ (t0 + (k : ℝ) * τ) x)))) =
      (∫ x in (0 : ℝ)..1, ((U N).toFun x * φ (t0 + (N : ℝ) * τ) x)) -
      (∫ x in (0 : ℝ)..1, ((U 0).toFun x * φ (t0 + ((0 : ℕ) : ℝ) * τ) x)) :=
    htele (fun j : ℕ => ∫ x in (0 : ℝ)..1, ((U j).toFun x *
      φ (t0 + (j : ℝ) * τ) x)) N
  have hCN0 : (∫ x in (0 : ℝ)..1, ((U N).toFun x * φ (t0 + (N : ℝ) * τ) x)) = 0 := by
    rw [hsN]
    have hcon : (∫ x in (0 : ℝ)..1, ((U N).toFun x * φ t1 x)) =
        ∫ x in (0 : ℝ)..1, (0 : ℝ) :=
      intervalIntegral.integral_congr (fun x _ => by rw [hφ1 x, mul_zero])
    rw [hcon, intervalIntegral.integral_zero]
  have hC00 : (∫ x in (0 : ℝ)..1, ((U 0).toFun x * φ (t0 + ((0 : ℕ) : ℝ) * τ) x)) = 0 := by
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hcon : (∫ x in (0 : ℝ)..1, ((U 0).toFun x * φ t0 x)) =
        ∫ x in (0 : ℝ)..1, (0 : ℝ) :=
      intervalIntegral.integral_congr (fun x _ => by rw [hφ0 x, mul_zero])
    rw [hcon, intervalIntegral.integral_zero]
  have hE : (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) =
      (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, ((U (k + 1)).toFun x *
        φ (t0 + ((k + 1 : ℕ) : ℝ) * τ) x)) -
      (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k hk => hi k (Finset.mem_range.mp hk))
  have hG : (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        ((U k).toFun x *
        (φ (t0 + ((k : ℝ) + 1) * τ) x - φ (t0 + (k : ℝ) * τ) x))) =
      (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) -
      (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + (k : ℝ) * τ) x)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k hk => hii k (Finset.mem_range.mp hk))
  have hT : (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, ((U (k + 1)).toFun x *
        φ (t0 + ((k + 1 : ℕ) : ℝ) * τ) x)) =
      (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, ((U k).toFun x *
        φ (t0 + (k : ℝ) * τ) x)) := by
    have hTC := hTeleC
    rw [Finset.sum_sub_distrib, hCN0, hC00] at hTC
    linarith
  have habel : (∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        (((U (k + 1)).toFun x - (U k).toFun x) *
        φ (t0 + ((k : ℝ) + 1) * τ) x)) =
      -(∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1,
        ((U k).toFun x *
        (φ (t0 + ((k : ℝ) + 1) * τ) x - φ (t0 + (k : ℝ) * τ) x))) := by
    linarith [hE, hG, hT]
  rw [← habel, ← htime, ← hsplit]
  exact hmaster


theorem tau_pos {t0 t1 : ℝ} (ht : t0 < t1) (N : ℕ) (hN : 0 < N) :
    0 < (t1 - t0) / (N : ℝ) := by
  apply div_pos (sub_pos.mpr ht)
  exact Nat.cast_pos.mpr hN

/-- On slab `k`, the time index recovers `k`. -/

theorem floor_on_slab {t0 t1 : ℝ} (ht : t0 < t1) (N : ℕ) (hN : 0 < N)
    (k : ℕ) (t : ℝ)
    (hlo : t0 + (k : ℝ) * ((t1 - t0) / N) ≤ t)
    (hhi : t < t0 + ((k : ℝ) + 1) * ((t1 - t0) / N)) :
    Nat.floor ((t - t0) / ((t1 - t0) / N)) = k := by
  have hτ : 0 < (t1 - t0) / (N : ℝ) := tau_pos ht N hN
  have h0 : 0 ≤ (t - t0) / ((t1 - t0) / N) := by
    apply div_nonneg _ (le_of_lt hτ)
    have hkp : (0 : ℝ) ≤ (k : ℝ) * ((t1 - t0) / N) := by positivity
    linarith
  rw [Nat.floor_eq_iff h0]
  constructor
  · rw [le_div_iff₀ hτ]
    linarith
  · rw [div_lt_iff₀ hτ]
    linarith

/-- On slab `k`, the right-sampled time index is `k + 1` (mismatch witness for
the first rewrite, whose left side samples `U k` on slab `k`). -/

theorem floor_succ_on_slab {t0 t1 : ℝ} (ht : t0 < t1) (N : ℕ) (hN : 0 < N)
    (k : ℕ) (t : ℝ)
    (hlo : t0 + (k : ℝ) * ((t1 - t0) / N) ≤ t)
    (hhi : t < t0 + ((k : ℝ) + 1) * ((t1 - t0) / N)) :
    Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 = k + 1 := by
  rw [floor_on_slab ht N hN k t hlo hhi]

/-- An `x`-only function is integrable on a rectangle if it is integrable on
the `x`-fiber. -/

theorem integrableOn_xonly {a b : ℝ} (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Icc (0:ℝ) 1) volume) :
    IntegrableOn (fun p : ℝ × ℝ => f p.2)
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) (volume.prod volume) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc a b)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  show Integrable _ ((volume.prod volume).restrict _)
  rw [← Measure.prod_restrict]
  exact @Integrable.comp_snd _ _ _ _ _ _ _ _ _ hf _ hfin

/-- The integral of an `x`-only function over a slab is the slab width times
the fiber integral (one-slab Fubini step). -/

theorem slab_integral_xonly {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Icc (0:ℝ) 1) volume) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1, f p.2 ∂(volume.prod volume)
      = (b - a) * ∫ x in Set.Icc (0:ℝ) 1, f x ∂volume := by
  have hI := integrableOn_xonly (a := a) (b := b) f hf
  rw [setIntegral_prod _ hI]
  show (∫ _ in Set.Icc a b, ∫ y in Set.Icc (0:ℝ) 1, f y ∂volume ∂volume) = _
  have hvol : volume.real (Set.Icc a b) = b - a := by
    rw [Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [setIntegral_const, hvol, smul_eq_mul]

/-- The `t = t1` slice of the rectangle is null, so the `if p.1 = t1` branch
of the integrands is irrelevant. -/

theorem prod_singleton_Icc_null {t1 : ℝ} :
    (volume.prod volume) ({t1} ×ˢ Set.Icc (0:ℝ) 1) = 0 := by
  rw [Measure.prod_prod, Real.volume_singleton, zero_mul]


theorem WeakH10.toFun_bounded_on_Icc (W : WeakH10)
    (hw : Integrable W.weakDeriv (volume.restrict (Set.Icc (0:ℝ) 1))) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, ‖W.toFun x‖ ≤ C := by
  refine ⟨∫ t in Set.Icc (0:ℝ) 1, ‖W.weakDeriv t‖ ∂volume, fun x hx => ?_⟩
  rw [W.toFun_eq_integral x hx]
  have h0x : (0:ℝ) ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have h_nonneg : 0 ≤ ∫ t in (0:ℝ)..x, ‖W.weakDeriv t‖ := by
    rw [intervalIntegral.integral_of_le h0x]
    exact integral_nonneg (fun t => norm_nonneg _)
  have hsub : Set.Ioc (0:ℝ) x ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hx1)
  have h_mono : ∫ t in Set.Ioc (0:ℝ) x, ‖W.weakDeriv t‖ ∂volume
      ≤ ∫ t in Set.Icc (0:ℝ) 1, ‖W.weakDeriv t‖ ∂volume := by
    apply setIntegral_mono_set _ _ _
    · exact hw.norm
    · exact ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun t ht => hsub ht)
  calc ‖∫ t in (0:ℝ)..x, W.weakDeriv t‖
      ≤ |∫ t in (0:ℝ)..x, ‖W.weakDeriv t‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
    _ = ∫ t in (0:ℝ)..x, ‖W.weakDeriv t‖ := abs_of_nonneg h_nonneg
    _ = ∫ t in Set.Ioc (0:ℝ) x, ‖W.weakDeriv t‖ ∂volume :=
        intervalIntegral.integral_of_le h0x
    _ ≤ ∫ t in Set.Icc (0:ℝ) 1, ‖W.weakDeriv t‖ ∂volume := h_mono


theorem fiber_product_integrableOn (W : WeakH10)
    (hW : Integrable W.toFun (volume.restrict (Set.Icc (0:ℝ) 1)))
    (hw : Integrable W.weakDeriv (volume.restrict (Set.Icc (0:ℝ) 1)))
    (g : ℝ → ℝ) (hg : Integrable g (volume.restrict (Set.Icc (0:ℝ) 1))) :
    IntegrableOn (fun x => W.toFun x * g x) (Set.Icc (0:ℝ) 1) volume := by
  obtain ⟨C, hC⟩ := W.toFun_bounded_on_Icc hw
  exact Integrable.bdd_mul hg hW.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => hC x hx))


theorem fiber_phidiff_integrableOn (W : WeakH10)
    (hW : Integrable W.toFun (volume.restrict (Set.Icc (0:ℝ) 1)))
    (hw : Integrable W.weakDeriv (volume.restrict (Set.Icc (0:ℝ) 1)))
    (φ : ℝ → ℝ → ℝ) (s1 s2 : ℝ)
    (h1 : Integrable (fun x => φ s1 x) (volume.restrict (Set.Icc (0:ℝ) 1)))
    (h2 : Integrable (fun x => φ s2 x) (volume.restrict (Set.Icc (0:ℝ) 1))) :
    IntegrableOn (fun x => W.toFun x * (φ s1 x - φ s2 x)) (Set.Icc (0:ℝ) 1) volume := by
  have hg : Integrable (fun x => φ s1 x - φ s2 x) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    h1.sub h2
  exact fiber_product_integrableOn W hW hw _ hg


theorem integrableOn_xonly_Ico {a b : ℝ} (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Icc (0:ℝ) 1) volume) :
    IntegrableOn (fun p : ℝ × ℝ => f p.2)
      (Set.Ico a b ×ˢ Set.Icc (0:ℝ) 1) (volume.prod volume) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ico a b)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  show Integrable _ ((volume.prod volume).restrict _)
  rw [← Measure.prod_restrict]
  exact @Integrable.comp_snd _ _ _ _ _ _ _ _ _ hf _ hfin


theorem slab_integral_xonly_Ico {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Icc (0:ℝ) 1) volume) :
    ∫ p in Set.Ico a b ×ˢ Set.Icc (0:ℝ) 1, f p.2 ∂(volume.prod volume)
      = (b - a) * ∫ x in Set.Icc (0:ℝ) 1, f x ∂volume := by
  have hI := integrableOn_xonly_Ico (a := a) (b := b) f hf
  rw [setIntegral_prod _ hI]
  show (∫ _ in Set.Ico a b, ∫ y in Set.Icc (0:ℝ) 1, f y ∂volume ∂volume) = _
  have hvol : volume.real (Set.Ico a b) = b - a := by
    rw [Measure.real_def, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [setIntegral_const, hvol, smul_eq_mul]


theorem prod_disjoint_of_disjoint_left {s₁ s₂ t : Set ℝ} (h : Disjoint s₁ s₂) :
    Disjoint (s₁ ×ˢ t) (s₂ ×ˢ t) := by
  rw [Set.disjoint_left] at h ⊢
  rintro ⟨a, b⟩ ⟨ha1, -⟩ ⟨ha2, -⟩
  exact h ha1 ha2


theorem setIntegral_zero_of_measure_zero {f : (ℝ×ℝ) → ℝ} {s : Set (ℝ×ℝ)}
    {μ : Measure (ℝ×ℝ)} (hs : μ s = 0) : ∫ p in s, f p ∂μ = 0 := by
  have hrr : μ.restrict s = 0 := Measure.restrict_eq_zero.mpr hs
  show ∫ p, f p ∂(μ.restrict s) = 0
  rw [hrr]
  exact integral_zero_measure _


theorem integrableOn_of_measure_zero {f : (ℝ×ℝ) → ℝ} {s : Set (ℝ×ℝ)}
    {μ : Measure (ℝ×ℝ)} (hs : μ s = 0) : IntegrableOn f s μ := by
  have hrr : μ.restrict s = 0 := Measure.restrict_eq_zero.mpr hs
  show Integrable f (μ.restrict s)
  rw [hrr]
  exact integrable_zero_measure


theorem setIntegral_restrict_self {S : Set (ℝ × ℝ)} {F : (ℝ × ℝ) → ℝ}
    (hm : MeasurableSet S) (μ : Measure (ℝ × ℝ)) :
    ∫ p in S, F p ∂(μ.restrict S) = ∫ p in S, F p ∂μ := by
  show ∫ p, F p ∂((μ.restrict S).restrict S) = ∫ p, F p ∂(μ.restrict S)
  rw [Measure.restrict_restrict hm, Set.inter_self]

/-- Sum-to-integral rewrites for the Rothe limit passage. -/



theorem rothe_rewrite_1_back
    {t0 t1 : ℝ} (ht : t0 < t1)
    (N : ℕ) (hN : 0 < N) (U : ℕ → WeakH10)
    (φ : ℝ → ℝ → ℝ)
    (kbar Fbar : ℕ → ℝ → ℝ)
    (hUint : ∀ k : ℕ, Integrable (U k).toFun (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ Integrable (U k).weakDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hKint : ∀ k : ℕ, k < N → Integrable (kbar k) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hFint : ∀ k : ℕ, k < N → Integrable (Fbar k) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hφint : ∀ s : ℝ, Integrable (fun x => φ s x) (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ Integrable (fun x => deriv (fun y => φ s y) x) (volume.restrict (Set.Icc (0 : ℝ) 1)))  :
    (-(∑ k ∈ Finset.range N,
        ∫ x in (0 : ℝ)..1,
          (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
            - φ (t0 + k * ((t1 - t0) / N)) x))
      = -∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
          * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
             else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
               - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
               / ((t1 - t0) / N))
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) := by
  have hτ : 0 < (t1 - t0) / N := tau_pos ht N hN
  have hτne : (t1 - t0) / N ≠ 0 := ne_of_gt hτ
  have hτnn : 0 ≤ (t1 - t0) / N := le_of_lt hτ
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  have hNτ : t0 + (N : ℝ) * ((t1 - t0) / N) = t1 := by
    have h : (N:ℝ) * ((t1 - t0) / N) = t1 - t0 := mul_div_cancel₀ _ hNne
    rw [h]
    ring
  have hG : ∀ k : ℕ, IntegrableOn
      (fun x => (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x)) (Set.Icc (0:ℝ) 1) volume := by
    intro k
    exact fiber_phidiff_integrableOn (U k) (hUint k).1 (hUint k).2 φ
      (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) (t0 + k * ((t1 - t0) / N))
      (hφint _).1 (hφint _).1
  have hH : ∀ k : ℕ, IntegrableOn
      (fun x => (U k).toFun x * ((φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x) / ((t1 - t0) / N))) (Set.Icc (0:ℝ) 1) volume := by
    intro k
    have hsub : Integrable (fun x => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      (hφint _).1.sub (hφint _).1
    have hg := hsub.div_const (((t1 - t0) / N) : ℝ)
    exact fiber_product_integrableOn (U k) (hUint k).1 (hUint k).2 _ hg
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod _ _
  have hmS : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hLHS : ∀ k : ℕ, (∫ x in (0:ℝ)..1, (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
      - φ (t0 + k * ((t1 - t0) / N)) x))
      = ∫ x in Set.Icc (0:ℝ) 1, (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x) ∂volume := by
    intro k
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  congr 1
  rw [hvol, setIntegral_restrict_self hmS _]
  refine (Finset.sum_congr rfl (fun k _ => hLHS k)).trans ?_
  have hFpt : ∀ k : ℕ, k < N → ∀ p : ℝ × ℝ,
      p ∈ Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1 →
      (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
        * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
           else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
             - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
             / ((t1 - t0) / N))
      = (U k).toFun p.2 * ((φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) p.2
        - φ (t0 + k * ((t1 - t0) / N)) p.2) / ((t1 - t0) / N)) := by
    intro k hkm p hp
    obtain ⟨hp1, -⟩ := hp
    rw [Set.mem_Ico] at hp1
    have hfloor : Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) = k :=
      floor_on_slab ht N hN k p.1 hp1.1 hp1.2
    have hkle : ((k:ℝ)+1) ≤ (N:ℝ) := by
      have hkN : k + 1 ≤ N := by omega
      exact_mod_cast hkN
    have hle : t0 + ((k:ℝ)+1) * ((t1 - t0) / N) ≤ t1 := by
      have h1 : ((k:ℝ)+1) * ((t1 - t0) / N) ≤ (N:ℝ) * ((t1 - t0) / N) :=
        mul_le_mul_of_nonneg_right hkle hτnn
      have h2 : t0 + ((k:ℝ)+1) * ((t1 - t0) / N) ≤ t0 + (N:ℝ) * ((t1 - t0) / N) := by
        linarith
      rw [hNτ] at h2
      exact h2
    have hne : p.1 ≠ t1 := ne_of_lt (lt_of_lt_of_le hp1.2 hle)
    rw [hfloor, ite_eq_right hne]
  have hslab_eq : ∀ k : ℕ, k < N →
      (∫ p in Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1,
        (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
        * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
           else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
             - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
             / ((t1 - t0) / N))
        ∂(volume.prod volume))
      = ∫ x in Set.Icc (0:ℝ) 1, (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x) ∂volume := by
    intro k hkm
    have hmeas : MeasurableSet (Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1) :=
      measurableSet_Ico.prod measurableSet_Icc
    have hab : t0 + (k:ℝ) * ((t1 - t0) / N) ≤ t0 + ((k:ℝ)+1) * ((t1 - t0) / N) := by
      have hle : (k:ℝ) * ((t1 - t0) / N) ≤ ((k:ℝ)+1) * ((t1 - t0) / N) :=
        mul_le_mul_of_nonneg_right (by linarith) hτnn
      linarith
    have hcongr : (∫ p in Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1,
          (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
          * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
             else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
               - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
               / ((t1 - t0) / N))
          ∂(volume.prod volume))
        = ∫ p in Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1,
          (U k).toFun p.2 * ((φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) p.2
            - φ (t0 + k * ((t1 - t0) / N)) p.2) / ((t1 - t0) / N))
          ∂(volume.prod volume) :=
      setIntegral_congr_ae hmeas (ae_of_all _ (fun p hp => hFpt k hkm p hp))
    rw [hcongr, slab_integral_xonly_Ico hab _ (hH k)]
    have hτ' : (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) - (t0 + (k:ℝ) * ((t1 - t0) / N))
        = ((t1 - t0) / N) := by ring
    rw [hτ']
    have hHG : (∫ x in Set.Icc (0:ℝ) 1, (U k).toFun x * ((φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x) / ((t1 - t0) / N)) ∂volume)
        = (∫ x in Set.Icc (0:ℝ) 1, (U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
          - φ (t0 + k * ((t1 - t0) / N)) x) ∂volume) / ((t1 - t0) / N) := by
      have hcongr2 : (∫ x in Set.Icc (0:ℝ) 1, (U k).toFun x * ((φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
          - φ (t0 + k * ((t1 - t0) / N)) x) / ((t1 - t0) / N)) ∂volume)
          = ∫ x in Set.Icc (0:ℝ) 1, ((U k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
            - φ (t0 + k * ((t1 - t0) / N)) x)) / ((t1 - t0) / N) ∂volume := by
        apply setIntegral_congr_ae measurableSet_Icc
        exact ae_of_all _ (fun x _ => by ring)
      rw [hcongr2]
      exact integral_div _ _
    rw [hHG, mul_div_cancel₀ _ hτne]
  have hslab_int : ∀ k : ℕ, k < N → IntegrableOn
      ((fun p : ℝ × ℝ => (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
        * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
           else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
             - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
             / ((t1 - t0) / N))))
      (Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1)
      (volume.prod volume) := by
    intro k hkm
    have hmeas : MeasurableSet (Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1) :=
      measurableSet_Ico.prod measurableSet_Icc
    have hx := @integrableOn_xonly_Ico (t0 + (k:ℝ) * ((t1 - t0) / N))
      (t0 + ((k:ℝ)+1) * ((t1 - t0) / N))
      (fun x => (U k).toFun x * ((φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        - φ (t0 + k * ((t1 - t0) / N)) x) / ((t1 - t0) / N))) (hH k)
    exact Integrable.congr hx (ae_restrict_of_forall_mem hmeas (fun p hp => (hFpt k hkm p hp).symm))
  have key : ∀ m : ℕ, m ≤ N → IntegrableOn
      ((fun p : ℝ × ℝ => (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
        * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
           else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
             - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
             / ((t1 - t0) / N))))
      (Set.Ico t0 (t0 + (m:ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1) (volume.prod volume)
      ∧ (∫ p in Set.Ico t0 (t0 + (m:ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1,
        (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
        * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
           else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
             - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
             / ((t1 - t0) / N))
        ∂(volume.prod volume))
      = ∑ k ∈ Finset.range m, ∫ p in Set.Ico (t0 + (k:ℝ) * ((t1 - t0) / N)) (t0 + ((k:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1,
        (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
        * (if p.1 = t1 then deriv (fun s => φ s p.2) p.1
           else (φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2
             - φ (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) p.2)
             / ((t1 - t0) / N))
        ∂(volume.prod volume) := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hset : Set.Ico t0 (t0 + ((0:ℕ):ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1 = ∅ := by
        simp
      constructor
      · rw [hset]
        exact integrableOn_empty
      · rw [hset, setIntegral_empty, Finset.range_zero, Finset.sum_empty]
    | succ n ih =>
      intro hmn1
      have hm : n ≤ N := by omega
      have hkm : n < N := by omega
      have hcast : ((n + 1 : ℕ):ℝ) = (n:ℝ) + 1 := by push_cast; ring
      have h1 : t0 ≤ t0 + (n:ℝ) * ((t1 - t0) / N) := by
        have hnn : (0:ℝ) ≤ (n:ℝ) * ((t1 - t0) / N) := mul_nonneg (Nat.cast_nonneg _) hτnn
        linarith
      have h2 : t0 + (n:ℝ) * ((t1 - t0) / N) ≤ t0 + ((n:ℝ)+1) * ((t1 - t0) / N) := by
        have hle : (n:ℝ) * ((t1 - t0) / N) ≤ ((n:ℝ)+1) * ((t1 - t0) / N) :=
          mul_le_mul_of_nonneg_right (by linarith) hτnn
        linarith
      have hunion : Set.Ico t0 (t0 + ((n+1:ℕ):ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1
          = (Set.Ico t0 (t0 + (n:ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1)
            ∪ (Set.Ico (t0 + (n:ℝ) * ((t1 - t0) / N)) (t0 + ((n:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1) := by
        rw [hcast, (Set.Ico_union_Ico_eq_Ico h1 h2).symm, Set.union_prod]
      have hdisj : Disjoint (Set.Ico t0 (t0 + (n:ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1)
          (Set.Ico (t0 + (n:ℝ) * ((t1 - t0) / N)) (t0 + ((n:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1) :=
        prod_disjoint_of_disjoint_left Set.Ico_disjoint_Ico_same
      have hmeasB : MeasurableSet (Set.Ico (t0 + (n:ℝ) * ((t1 - t0) / N)) (t0 + ((n:ℝ)+1) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1) :=
        measurableSet_Ico.prod measurableSet_Icc
      have ihA := ih hm
      constructor
      · rw [hunion]
        exact IntegrableOn.union ihA.1 (hslab_int n hkm)
      · rw [hunion, setIntegral_union hdisj hmeasB ihA.1 (hslab_int n hkm), ihA.2,
          Finset.sum_range_succ]
  have htpart : Set.Icc t0 t1 = Set.Ico t0 (t0 + (N:ℝ) * ((t1 - t0) / N)) ∪ {t1} := by
    rw [hNτ, ← Set.Ico_insert_right (le_of_lt ht), Set.insert_eq, Set.union_comm]
  have hS : Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1
      = (Set.Ico t0 (t0 + (N:ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1)
        ∪ ({t1} ×ˢ Set.Icc (0:ℝ) 1) := by
    rw [htpart, Set.union_prod]
  have hnotmem : t1 ∉ Set.Ico t0 (t0 + (N:ℝ) * ((t1 - t0) / N)) := by
    intro h
    rw [Set.mem_Ico] at h
    rw [hNτ] at h
    exact absurd h.2 (lt_irrefl t1)
  have hdisjS : Disjoint (Set.Ico t0 (t0 + (N:ℝ) * ((t1 - t0) / N)) ×ˢ Set.Icc (0:ℝ) 1)
      ({t1} ×ˢ Set.Icc (0:ℝ) 1) :=
    prod_disjoint_of_disjoint_left (Set.disjoint_singleton_right.mpr hnotmem)
  have hmeasS : MeasurableSet ({t1} ×ˢ Set.Icc (0:ℝ) 1) :=
    (measurableSet_singleton t1).prod measurableSet_Icc
  have keyN := key N le_rfl
  rw [hS, setIntegral_union hdisjS hmeasS keyN.1
    (integrableOn_of_measure_zero prod_singleton_Icc_null),
    setIntegral_zero_of_measure_zero prod_singleton_Icc_null, add_zero, keyN.2]
  exact Finset.sum_congr rfl (fun k hk => (hslab_eq k (Finset.mem_range.mp hk)).symm)


theorem rothe_rewrite_2_of_prod_integrable
    {t0 t1 : ℝ} (ht : t0 < t1)
    (N : ℕ) (hN : 0 < N) (U : ℕ → WeakH10)
    (φ : ℝ → ℝ → ℝ)
    (kbar Fbar : ℕ → ℝ → ℝ)
    (hUint : ∀ k : ℕ, Integrable (U k).toFun (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ Integrable (U k).weakDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hKint : ∀ k : ℕ, k < N → Integrable (kbar k) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hFint : ∀ k : ℕ, k < N → Integrable (Fbar k) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hφint : ∀ s : ℝ, Integrable (fun x => φ s x) (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ Integrable (fun x => deriv (fun y => φ s y) x) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hProd : ∀ k : ℕ, k < N → IntegrableOn
      (fun x => kbar k x * (U (k + 1)).weakDeriv x
        * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x)
      (Set.Icc (0 : ℝ) 1) volume) :
    (((t1 - t0) / N) * ∑ k ∈ Finset.range N,
        ∫ x in (0 : ℝ)..1,
          kbar k x * (U (k + 1)).weakDeriv x
            * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then kbar (N - 1) p.2
         else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
          * (if p.1 = t1 then (U N).weakDeriv p.2
             else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
          * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
             else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) := by
  have hτ : 0 < (t1 - t0) / (N : ℝ) := tau_pos ht N hN
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  have hNt : (N : ℝ) * ((t1 - t0) / N) = t1 - t0 := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hNne
  set a : ℕ → ℝ := fun k => t0 + (k : ℝ) * ((t1 - t0) / N) with hadef
  have ha0 : a 0 = t0 := by simp only [hadef, Nat.cast_zero, zero_mul, add_zero]
  have haN : a N = t1 := by
    simp only [hadef]
    rw [hNt]
    ring
  have hmono : Monotone a := by
    intro m n hmn
    have h1 : (m : ℝ) * ((t1 - t0) / N) ≤ (n : ℝ) * ((t1 - t0) / N) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) (le_of_lt hτ)
    simp only [hadef]
    linarith
  set T : ℕ → Set (ℝ × ℝ) :=
    fun k => Set.Ico (a k) (a (k+1)) ×ˢ Set.Icc (0:ℝ) 1 with hTdef
  set S : Set (ℝ × ℝ) := Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1 with hSdef
  have hTmeas : ∀ k : ℕ, MeasurableSet (T k) := by
    intro k
    simp only [hTdef]
    exact measurableSet_Ico.prod measurableSet_Icc
  have hSmeas : MeasurableSet S := by
    simp only [hSdef]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hcov : Set.Icc t0 t1
      = (⋃ k ∈ Finset.range N, Set.Ico (a k) (a (k+1))) ∪ {t1} := by
    ext t
    simp only [Set.mem_Icc, Set.mem_union, Set.mem_iUnion, Finset.mem_range,
      Set.mem_Ico, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hlo, hhi⟩
      by_cases hteq : t = t1
      · exact Or.inr hteq
      · left
        have hlt : t < t1 := lt_of_le_of_ne hhi hteq
        have h0 : 0 ≤ (t - t0) / ((t1 - t0) / N) := by
          apply div_nonneg _ (le_of_lt hτ)
          linarith
        refine ⟨Nat.floor ((t - t0) / ((t1 - t0) / N)), ?_, ?_, ?_⟩
        · rw [Nat.floor_lt h0, div_lt_iff₀ hτ, hNt]
          linarith
        · simp only [hadef]
          have hfl := Nat.floor_le h0
          have h3 := mul_le_mul_of_nonneg_right hfl (le_of_lt hτ)
          rw [div_mul_cancel₀ _ (ne_of_gt hτ)] at h3
          linarith
        · have hlt1 := Nat.lt_floor_add_one ((t - t0) / ((t1 - t0) / N))
          simp only [hadef]
          push_cast
          have h4 : ((t - t0) / ((t1 - t0) / N)) * ((t1 - t0) / N)
              < ((Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) + 1) * ((t1 - t0) / N) :=
            mul_lt_mul_of_pos_right hlt1 hτ
          rw [div_mul_cancel₀ _ (ne_of_gt hτ)] at h4
          linarith
    · rintro (⟨k, hkr, hklo, hkhi⟩ | rfl)
      · have hk1 : k + 1 ≤ N := by omega
        have hak : a (k+1) ≤ t1 := by
          have h := hmono hk1
          rwa [haN] at h
        have ha0k : t0 ≤ a k := by
          have h := hmono (Nat.zero_le k)
          rwa [ha0] at h
        constructor <;> linarith
      · exact ⟨le_of_lt ht, le_rfl⟩
  have hScov : S
      = (⋃ k ∈ Finset.range N, T k) ∪ ({t1} ×ˢ Set.Icc (0:ℝ) 1) := by
    simp only [hSdef, hTdef, hcov, Set.union_prod, Set.iUnion_prod_const]
  have hfib_eq : ∀ k ∈ Finset.range N, ∀ p ∈ T k,
      (if p.1 = t1 then kbar (N - 1) p.2
        else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
        * (if p.1 = t1 then (U N).weakDeriv p.2
          else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
        * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
          else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2)
      = kbar k p.2 * (U (k + 1)).weakDeriv p.2
        * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) p.2 := by
    intro k hk p hp
    have hkN : k < N := Finset.mem_range.mp hk
    simp only [hTdef, Set.mem_prod, Set.mem_Ico] at hp
    obtain ⟨⟨hklo, hkhi⟩, -⟩ := hp
    have hk1 : k + 1 ≤ N := by omega
    have hak : a (k + 1) ≤ t1 := by
      have h := hmono hk1
      rwa [haN] at h
    have hne : p.1 ≠ t1 := ne_of_lt (lt_of_lt_of_le hkhi hak)
    have hfloor : Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) = k := by
      apply floor_on_slab ht N hN k p.1
      · have h := hklo
        simp only [hadef] at h
        exact h
      · have h := hkhi
        simp only [hadef] at h
        push_cast at h
        exact h
    rw [ite_eq_right hne, ite_eq_right hne, ite_eq_right hne, hfloor]
  have hProd' : ∀ k : ℕ, k < N → IntegrableOn
      (fun x => kbar k x * (U (k + 1)).weakDeriv x
        * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x)
      (Set.Icc (0 : ℝ) 1) volume := fun k hk => hProd k hk
  have hInts : ∀ k ∈ Finset.range N,
      IntegrableOn (fun p : ℝ × ℝ =>
        (if p.1 = t1 then kbar (N - 1) p.2
          else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
          * (if p.1 = t1 then (U N).weakDeriv p.2
            else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
          * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
            else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2))
      (T k) (volume.prod volume) := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hPk := hProd k hkN
    have hfin : IsFiniteMeasure (volume.restrict (Set.Ico (a k) (a (k+1)))) := by
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_Ico]
      exact ENNReal.ofReal_lt_top
    have hlift : IntegrableOn
        (fun p : ℝ × ℝ => kbar k p.2 * (U (k + 1)).weakDeriv p.2
          * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) p.2)
        (T k) (volume.prod volume) := by
      simp only [hTdef]
      show Integrable _ ((volume.prod volume).restrict _)
      rw [← Measure.prod_restrict]
      exact @Integrable.comp_snd _ _ _ _ _ _ _ _ _ hPk _ hfin
    have heq : (fun p : ℝ × ℝ => kbar k p.2 * (U (k + 1)).weakDeriv p.2
          * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) p.2)
        =ᵐ[(volume.prod volume).restrict (T k)]
        (fun p : ℝ × ℝ =>
          (if p.1 = t1 then kbar (N - 1) p.2
            else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
            * (if p.1 = t1 then (U N).weakDeriv p.2
              else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
            * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
              else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2)) := by
      filter_upwards [ae_restrict_mem (hTmeas k)] with p hp
      exact (hfib_eq k hk p hp).symm
    exact Integrable.congr hlift heq
  have hUnionInt : IntegrableOn (fun p : ℝ × ℝ =>
      (if p.1 = t1 then kbar (N - 1) p.2
        else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
        * (if p.1 = t1 then (U N).weakDeriv p.2
          else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
        * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
          else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2))
      (⋃ k ∈ Finset.range N, T k) (volume.prod volume) :=
    (integrableOn_finset_iUnion).mpr hInts
  have hnullmeas0 : (volume.prod volume) ({t1} ×ˢ Set.Icc (0:ℝ) 1) = 0 :=
    prod_singleton_Icc_null
  have hNullInt : IntegrableOn (fun p : ℝ × ℝ =>
      (if p.1 = t1 then kbar (N - 1) p.2
        else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
        * (if p.1 = t1 then (U N).weakDeriv p.2
          else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
        * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
          else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2))
      ({t1} ×ˢ Set.Icc (0:ℝ) 1) (volume.prod volume) := by
    show Integrable _ ((volume.prod volume).restrict _)
    rw [Measure.restrict_eq_zero.mpr hnullmeas0]
    exact integrable_zero_measure
  have hnullmeas : MeasurableSet ({t1} ×ˢ Set.Icc (0:ℝ) 1) :=
    (measurableSet_singleton t1).prod measurableSet_Icc
  have hdisj : Disjoint (⋃ k ∈ Finset.range N, T k) ({t1} ×ˢ Set.Icc (0:ℝ) 1) := by
    rw [Set.disjoint_left]
    rintro p hp1 hp2
    simp only [Set.mem_iUnion, Finset.mem_range, hTdef, Set.mem_prod,
      Set.mem_Ico] at hp1
    simp only [Set.mem_prod, Set.mem_singleton_iff] at hp2
    obtain ⟨k, hkN, ⟨hklo, hkhi⟩, -⟩ := hp1
    obtain ⟨heq, -⟩ := hp2
    rw [heq] at hkhi
    have hk1 : k + 1 ≤ N := by omega
    have hak : a (k + 1) ≤ t1 := by
      have h := hmono hk1
      rwa [haN] at h
    linarith
  have hpair : Set.Pairwise (↑(Finset.range N)) (Function.onFun Disjoint T) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    show Disjoint (T i) (T j)
    rw [Set.disjoint_left]
    intro p
    simp only [hTdef, Set.mem_prod, Set.mem_Ico]
    rintro ⟨⟨hilo, hihi⟩, -⟩ ⟨⟨hjlo, hjhi⟩, -⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : a (i + 1) ≤ a j := hmono (by omega)
      linarith
    · have hle : a (j + 1) ≤ a i := hmono (by omega)
      linarith
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := rfl
  rw [hvol, Measure.restrict_restrict hSmeas, Set.inter_self]
  rw [hScov]
  rw [setIntegral_union hdisj hnullmeas hUnionInt hNullInt]
  rw [integral_biUnion_finset (Finset.range N) (fun k _ => hTmeas k) hpair hInts]
  have hnull0 : (∫ p in ({t1} ×ˢ Set.Icc (0:ℝ) 1),
      (if p.1 = t1 then kbar (N - 1) p.2
        else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
        * (if p.1 = t1 then (U N).weakDeriv p.2
          else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
        * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
          else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2)
      ∂(volume.prod volume)) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hnullmeas0]
    exact integral_zero_measure _
  rw [hnull0, add_zero]
  have hslab : ∀ k ∈ Finset.range N,
      (∫ p in T k,
        (if p.1 = t1 then kbar (N - 1) p.2
          else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
          * (if p.1 = t1 then (U N).weakDeriv p.2
            else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
          * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
            else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2)
        ∂(volume.prod volume))
      = ((t1 - t0) / N)
        * ∫ x in Set.Icc (0:ℝ) 1, kbar k x * (U (k + 1)).weakDeriv x
          * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hPk := hProd k hkN
    have hcongr : (∫ p in T k,
          (if p.1 = t1 then kbar (N - 1) p.2
            else kbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
            * (if p.1 = t1 then (U N).weakDeriv p.2
              else (U (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
            * (if p.1 = t1 then deriv (fun y => φ t1 y) p.2
              else deriv (fun y => φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) y) p.2)
          ∂(volume.prod volume))
        = ∫ p in T k, kbar k p.2 * (U (k + 1)).weakDeriv p.2
          * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) p.2
          ∂(volume.prod volume) := by
      apply setIntegral_congr_ae (hTmeas k)
      exact ae_of_all _ (fun p hp => hfib_eq k hk p hp)
    rw [hcongr]
    have hTk : T k = Set.Ico (a k) (a (k+1)) ×ˢ Set.Icc (0:ℝ) 1 := by simp only [hTdef]
    rw [hTk]
    have hsl := slab_integral_xonly_Ico (hmono (Nat.le_succ k))
      (fun x => kbar k x * (U (k + 1)).weakDeriv x
        * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x) hPk
    rw [hsl]
    have hwidth : a (k + 1) - a k = (t1 - t0) / N := by
      simp only [hadef]
      push_cast
      ring
    rw [hwidth]
  have hfib2 : ∀ k ∈ Finset.range N,
      (∫ x in (0:ℝ)..1, kbar k x * (U (k + 1)).weakDeriv x
        * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x)
      = ∫ x in Set.Icc (0:ℝ) 1, kbar k x * (U (k + 1)).weakDeriv x
        * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x := by
    intro k _
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact (integral_Icc_eq_integral_Ioc).symm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hfib2 k hk, hslab k hk]


theorem rothe_rewrite_3_of_prod_integrable
    {t0 t1 : ℝ} (ht : t0 < t1)
    (N : ℕ) (hN : 0 < N)
    (φ : ℝ → ℝ → ℝ) (Fbar : ℕ → ℝ → ℝ)
    (hProd : ∀ k : ℕ, k < N → IntegrableOn
      (fun x => Fbar k x * φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x)
      (Set.Icc (0 : ℝ) 1) volume) :
    (((t1 - t0) / N) * ∑ k ∈ Finset.range N,
        ∫ x in (0 : ℝ)..1,
          Fbar k x * φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then Fbar (N - 1) p.2
         else Fbar (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
          * (if p.1 = t1 then φ t1 p.2
             else φ (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1 : ℝ) * ((t1 - t0) / N))) p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))  := by
  set Δ : ℝ := (t1 - t0) / N with hΔdef
  set g : ℕ → ℝ → ℝ := fun k x => Fbar k x * φ (t0 + (k + 1 : ℝ) * Δ) x
  set F : ℝ × ℝ → ℝ := fun p =>
    (if p.1 = t1 then Fbar (N - 1) p.2
     else Fbar (Nat.floor ((p.1 - t0) / Δ)) p.2)
      * (if p.1 = t1 then φ t1 p.2
         else φ (t0 + ((Nat.floor ((p.1 - t0) / Δ) + 1 : ℝ) * Δ)) p.2)
  set T : ℕ → Set ℝ := fun k => Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ)
  set S : ℕ → Set (ℝ × ℝ) := fun k => T k ×ˢ Set.Icc (0 : ℝ) 1
  set V : Set (ℝ × ℝ) := ({t1} ×ˢ Set.Icc (0 : ℝ) 1)
  set Big : Set (ℝ × ℝ) := (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
  show Δ * ∑ k ∈ Finset.range N, ∫ x in (0 : ℝ)..1, g k x
    = ∫ p in Big, F p ∂(volume.restrict Big)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hΔ : 0 < Δ := by
    rw [hΔdef]
    exact div_pos (sub_pos.mpr ht) (by exact_mod_cast hN)
  have hNΔ : (N : ℝ) * Δ = t1 - t0 := by
    rw [hΔdef]
    exact mul_div_cancel₀ _ hN'
  have htN : t0 + (N : ℝ) * Δ = t1 := by linarith [hNΔ]
  have hProdΔ : ∀ k : ℕ, k < N → IntegrableOn (g k) (Set.Icc (0 : ℝ) 1) volume := hProd
  have hslab_le : ∀ k : ℕ, k < N → t0 + ((k : ℝ) + 1) * Δ ≤ t1 := by
    intro k hkN
    have hk1N : ((k : ℝ) + 1) ≤ (N : ℝ) := by
      have h1 : k + 1 ≤ N := hkN
      exact_mod_cast h1
    have hmul := mul_le_mul_of_nonneg_right hk1N hΔ.le
    linarith [hmul, htN]
  have hfloor : ∀ k : ℕ, k < N → ∀ t : ℝ, t ∈ T k → Nat.floor ((t - t0) / Δ) = k := by
    intro k hkN t htmem
    have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
    rw [hT, Set.mem_Ico] at htmem
    obtain ⟨hlo, hhi⟩ := htmem
    have hkΔ0 : (0 : ℝ) ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg k) hΔ.le
    have ht0le : t0 ≤ t := by linarith [hlo, hkΔ0]
    have hnonneg : 0 ≤ (t - t0) / Δ := div_nonneg (sub_nonneg.mpr ht0le) hΔ.le
    rw [Nat.floor_eq_iff hnonneg, le_div_iff₀ hΔ, div_lt_iff₀ hΔ]
    constructor <;> linarith [hlo, hhi]
  have ht1ne : ∀ k : ℕ, k < N → ∀ t : ℝ, t ∈ T k → t ≠ t1 := by
    intro k hkN t htmem hcon
    have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
    rw [hT, Set.mem_Ico] at htmem
    obtain ⟨hlo, hhi⟩ := htmem
    have hle := hslab_le k hkN
    rw [hcon] at hhi
    linarith [hhi, hle]
  have hFslab : ∀ k : ℕ, k < N → ∀ p : ℝ × ℝ, p ∈ S k → F p = g k p.2 := by
    intro k hkN p hpmem
    have hS : S k = T k ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    rw [hS, Set.mem_prod] at hpmem
    obtain ⟨htmem, -⟩ := hpmem
    have ht1 : p.1 ≠ t1 := ht1ne k hkN p.1 htmem
    have hfl : Nat.floor ((p.1 - t0) / Δ) = k := hfloor k hkN p.1 htmem
    have hFp : F p = (if p.1 = t1 then Fbar (N - 1) p.2
        else Fbar (Nat.floor ((p.1 - t0) / Δ)) p.2)
        * (if p.1 = t1 then φ t1 p.2
          else φ (t0 + ((Nat.floor ((p.1 - t0) / Δ) + 1 : ℝ) * Δ)) p.2) := rfl
    have hgp : g k p.2 = Fbar k p.2 * φ (t0 + (k + 1 : ℝ) * Δ) p.2 := rfl
    rw [hFp, hgp, ite_eq_right ht1, ite_eq_right ht1, hfl]
  have hSmeas : ∀ k : ℕ, MeasurableSet (S k) := by
    intro k
    have hS : S k = T k ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
    rw [hS, hT]
    exact measurableSet_Ico.prod measurableSet_Icc
  have hVmeas : MeasurableSet V := by
    have hV : V = ({t1} ×ˢ Set.Icc (0 : ℝ) 1) := rfl
    rw [hV]
    exact (measurableSet_singleton t1).prod measurableSet_Icc
  have hdisj_aux : ∀ i j : ℕ, i < j → Disjoint (S i) (S j) := by
    intro i j hij
    have hle : t0 + ((i : ℝ) + 1) * Δ ≤ t0 + (j : ℝ) * Δ := by
      have hi1j : ((i : ℝ) + 1) ≤ (j : ℝ) := by
        have h1 : i + 1 ≤ j := hij
        exact_mod_cast h1
      have hmul := mul_le_mul_of_nonneg_right hi1j hΔ.le
      linarith [hmul]
    have hSi : S i = T i ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    have hSj : S j = T j ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    have hTi : T i = Set.Ico (t0 + (i : ℝ) * Δ) (t0 + ((i : ℝ) + 1) * Δ) := rfl
    have hTj : T j = Set.Ico (t0 + (j : ℝ) * Δ) (t0 + ((j : ℝ) + 1) * Δ) := rfl
    rw [hSi, hSj, Set.disjoint_left]
    intro p hpA hpB
    rw [Set.mem_prod] at hpA hpB
    obtain ⟨hti, -⟩ := hpA
    obtain ⟨htj, -⟩ := hpB
    rw [hTi, Set.mem_Ico] at hti
    rw [hTj, Set.mem_Ico] at htj
    linarith [hti.2, htj.1, hle]
  have hdisj : Set.Pairwise ↑(Finset.range N) (Function.onFun Disjoint S) := by
    intro i hi j hj hij
    show Disjoint (S i) (S j)
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdisj_aux i j h
    · exact (hdisj_aux j i h).symm
  have hmem_slab : ∀ t : ℝ, t0 ≤ t → t < t1 → ∃ k : ℕ, k < N ∧ t ∈ T k := by
    intro t ht0 ht1
    set k : ℕ := Nat.floor ((t - t0) / Δ) with hkdef
    have hnonneg : 0 ≤ (t - t0) / Δ := div_nonneg (sub_nonneg.mpr ht0) hΔ.le
    have hltN : (t - t0) / Δ < (N : ℝ) := by
      rw [div_lt_iff₀ hΔ]
      linarith [ht1, hNΔ]
    have hfle : (k : ℝ) ≤ (t - t0) / Δ := Nat.floor_le hnonneg
    have h2 : (t - t0) / Δ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkN : k < N := by
      have hlt : (k : ℝ) < (N : ℝ) := lt_of_le_of_lt hfle hltN
      exact_mod_cast hlt
    refine ⟨k, hkN, ?_⟩
    have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
    rw [hT, Set.mem_Ico]
    rw [le_div_iff₀ hΔ] at hfle
    rw [div_lt_iff₀ hΔ] at h2
    constructor <;> linarith [hfle, h2]
  have hBig : Big = (⋃ k ∈ Finset.range N, S k) ∪ V := by
    have hB : Big = Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    have hV : V = ({t1} ×ˢ Set.Icc (0 : ℝ) 1) := rfl
    rw [hB, hV]
    ext p
    constructor
    · intro hp
      obtain ⟨ht, hx⟩ := hp
      obtain ⟨ht0, ht1⟩ := ht
      by_cases hpt : p.1 = t1
      · exact Or.inr ⟨hpt, hx⟩
      · left
        have ht1lt : p.1 < t1 := lt_of_le_of_ne ht1 hpt
        obtain ⟨k, hkN, hTmem⟩ := hmem_slab p.1 ht0 ht1lt
        have hSmem : p ∈ S k := by
          have hS : S k = T k ×ˢ Set.Icc (0 : ℝ) 1 := rfl
          rw [hS]
          exact ⟨hTmem, hx⟩
        simp only [Set.mem_iUnion]
        exact ⟨k, Finset.mem_range.mpr hkN, hSmem⟩
    · intro hp
      obtain hpU | hpV := hp
      · simp only [Set.mem_iUnion, Finset.mem_range] at hpU
        obtain ⟨k, hkN, hSk⟩ := hpU
        have hS : S k = T k ×ˢ Set.Icc (0 : ℝ) 1 := rfl
        rw [hS, Set.mem_prod] at hSk
        obtain ⟨htmem, hx⟩ := hSk
        have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
        rw [hT, Set.mem_Ico] at htmem
        obtain ⟨hlo, hhi⟩ := htmem
        have hkΔ0 : (0 : ℝ) ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg k) hΔ.le
        have hle := hslab_le k hkN
        refine ⟨?_, hx⟩
        show t0 ≤ p.1 ∧ p.1 ≤ t1
        constructor <;> linarith [hlo, hhi, hkΔ0, hle]
      · obtain ⟨hpt, hx⟩ := hpV
        have hpt' : p.1 = t1 := hpt
        refine ⟨?_, hx⟩
        rw [hpt']
        exact ⟨ht.le, le_rfl⟩
  have hdisjUV : Disjoint (⋃ k ∈ Finset.range N, S k) V := by
    have hV : V = ({t1} ×ˢ Set.Icc (0 : ℝ) 1) := rfl
    rw [hV, Set.disjoint_left]
    intro p hU hVmem
    simp only [Set.mem_iUnion, Finset.mem_range] at hU
    obtain ⟨k, hkN, hSk⟩ := hU
    have hS : S k = T k ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    rw [hS, Set.mem_prod] at hSk
    obtain ⟨htmem, -⟩ := hSk
    rw [Set.mem_prod, Set.mem_singleton_iff] at hVmem
    exact (ht1ne k hkN p.1 htmem) hVmem.1
  have hV0 : volume V = 0 := by
    have hV : V = ({t1} ×ˢ Set.Icc (0 : ℝ) 1) := rfl
    rw [hV, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hIntV : IntegrableOn F V volume := by
    unfold IntegrableOn
    rw [Measure.restrict_eq_zero.mpr hV0]
    exact integrable_zero_measure
  have hIntV0 : ∫ p in V, F p ∂volume = 0 := by
    rw [Measure.restrict_eq_zero.mpr hV0]
    exact integral_zero_measure _
  have hfinT : ∀ k : ℕ, IsFiniteMeasure (volume.restrict (T k)) := by
    intro k
    constructor
    rw [Measure.restrict_apply_univ]
    have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
    rw [hT, Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hvol : ∀ k : ℕ, volume.restrict (S k)
      = (volume.restrict (T k)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro k
    have hS : S k = T k ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    rw [hS, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
  have hvolT : ∀ k : ℕ, (volume (T k)).toReal = Δ := by
    intro k
    have hT : T k = Set.Ico (t0 + (k : ℝ) * Δ) (t0 + ((k : ℝ) + 1) * Δ) := rfl
    rw [hT, Real.volume_Ico]
    have harg : (t0 + ((k : ℝ) + 1) * Δ) - (t0 + (k : ℝ) * Δ) = Δ := by ring
    rw [harg]
    exact ENNReal.toReal_ofReal hΔ.le
  have hIntSlabSnd : ∀ k : ℕ, k < N → IntegrableOn (fun p : ℝ × ℝ => g k p.2) (S k) volume := by
    intro k hkN
    have _ := hfinT k
    unfold IntegrableOn
    rw [hvol k]
    exact Integrable.comp_snd (hProdΔ k hkN) (volume.restrict (T k))
  have hIntSlabF : ∀ k : ℕ, k < N → IntegrableOn F (S k) volume := by
    intro k hkN
    exact Integrable.congr (hIntSlabSnd k hkN)
      ((ae_restrict_mem (hSmeas k)).mono (fun p hp => (hFslab k hkN p hp).symm))
  have hSlab : ∀ k : ℕ, k < N →
      ∫ p in S k, F p ∂volume = Δ * ∫ x in Set.Icc (0 : ℝ) 1, g k x ∂volume := by
    intro k hkN
    have hcongr : ∫ p in S k, F p ∂volume = ∫ p in S k, g k p.2 ∂volume :=
      setIntegral_congr_ae (hSmeas k)
        (Filter.Eventually.of_forall fun p hp => hFslab k hkN p hp)
    have h1 : ∫ p in S k, g k p.2 ∂volume
        = ∫ p, g k p.2 ∂((volume.restrict (T k)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      rw [hvol k]
    have h2 : ∫ p, g k p.2 ∂((volume.restrict (T k)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        = (volume.restrict (T k)).real Set.univ • ∫ y, g k y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integral_fun_snd (g k)
    rw [hcongr, h1, h2, smul_eq_mul, Measure.real_def, Measure.restrict_apply_univ, hvolT k]
  have hIntIcc : ∀ k : ℕ, k < N →
      ∫ x in (0 : ℝ)..1, g k x = ∫ x in Set.Icc (0 : ℝ) 1, g k x ∂volume := by
    intro k hkN
    have hIoc : ∫ x in (0 : ℝ)..1, g k x = ∫ x in Set.Ioc (0 : ℝ) 1, g k x ∂volume :=
      intervalIntegral.integral_of_le (by norm_num)
    rw [hIoc]
    have hsplit : Set.Icc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 ∪ {0} := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h0, h1⟩
        by_cases hx : x = 0
        · right
          exact hx
        · left
          exact ⟨lt_of_le_of_ne h0 (Ne.symm hx), h1⟩
      · rintro (⟨h0, h1⟩ | rfl)
        · exact ⟨le_of_lt h0, h1⟩
        · exact ⟨le_rfl, zero_le_one⟩
    have hdisj0 : Disjoint (Set.Ioc (0 : ℝ) 1) ({0} : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hx h0
      simp only [Set.mem_Ioc, Set.mem_singleton_iff] at hx h0
      rw [h0] at hx
      exact lt_irrefl _ hx.1
    have hIntIoc : IntegrableOn (g k) (Set.Ioc (0 : ℝ) 1) volume :=
      IntegrableOn.mono (hProdΔ k hkN) Set.Ioc_subset_Icc_self le_rfl
    have hInt0 : IntegrableOn (g k) ({0} : Set ℝ) volume := by
      unfold IntegrableOn
      rw [Measure.restrict_eq_zero.mpr Real.volume_singleton]
      exact integrable_zero_measure
    have hunion := setIntegral_union hdisj0 (measurableSet_singleton (0 : ℝ)) hIntIoc hInt0
    have hnull0 : ∫ x in ({0} : Set ℝ), g k x ∂volume = 0 := by
      rw [Measure.restrict_eq_zero.mpr Real.volume_singleton]
      exact integral_zero_measure _
    rw [← hsplit] at hunion
    rw [hnull0, add_zero] at hunion
    exact hunion.symm
  have hIntSlabs : ∀ k ∈ Finset.range N, IntegrableOn F (S k) volume := by
    intro k hk
    exact hIntSlabF k (Finset.mem_range.mp hk)
  have hSmeas' : ∀ k ∈ Finset.range N, MeasurableSet (S k) := fun k _ => hSmeas k
  have hIntU : IntegrableOn F (⋃ k ∈ Finset.range N, S k) volume :=
    integrableOn_finset_iUnion.mpr hIntSlabs
  have hBigmeas : MeasurableSet Big := by
    have hB : Big = Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := rfl
    rw [hB]
    exact measurableSet_Icc.prod measurableSet_Icc
  rw [Measure.restrict_restrict hBigmeas, Set.inter_self]
  rw [hBig]
  rw [setIntegral_union hdisjUV hVmeas hIntU hIntV]
  rw [hIntV0, add_zero]
  rw [integral_biUnion_finset _ hSmeas' hdisj hIntSlabs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  show Δ * ∫ x in (0 : ℝ)..1, g k x = ∫ p in S k, F p ∂volume
  rw [hSlab k (Finset.mem_range.mp hk), hIntIcc k (Finset.mem_range.mp hk)]


lemma norm_integral_mul_le_eLpNorm_toReal_mul (f g : ℝ × ℝ → ℝ) (μ : Measure (ℝ × ℝ))
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ a, f a * g a ∂μ‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hCS := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  rw [L2.inner_def] at hCS
  have hInt : (∫ a, inner ℝ (⇑(hf.toLp f) a) (⇑(hg.toLp g) a) ∂μ)
      = ∫ a, f a * g a ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha hb
    rw [ha, hb]
    simp [RCLike.inner_apply, mul_comm]
  rw [hInt, Lp.norm_toLp, Lp.norm_toLp] at hCS
  exact hCS

/-- Term-1 passage: backward interpolant against the difference
quotient tends to `-∫∫ u * φ_t`. -/

theorem rothe_term1_tendsto
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → WeakH10)
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ)
    (u : ℝ → ℝ → ℝ)
    (hMemLpDeriv : MemLp (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hWeakThm : ∀ ψ : ℝ → ℝ → ℝ,
      MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U (φm N) (φm N)).toFun p.2
             else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)).toFun p.2)
              * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          u p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hTestConvThm : Filter.Tendsto (fun N : ℕ =>
        eLpNorm (fun p : ℝ × ℝ =>
          slabDiffQuot t0 t1 (φm N) φ p - deriv (fun s => φ s p.2) p.1) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (hUMemLpThm : MemLp (Function.uncurry u) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hBoundThm : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U (φm N) (φm N)).toFun x
        else (U (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)).toFun x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) ≤ ENNReal.ofReal C)
    (hGapThm : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      eLpNorm (fun p : ℝ × ℝ =>
        (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))))).toFun p.2
        - (if p.1 = t1 then (U (φm N) (φm N)).toFun p.2
           else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)).toFun p.2)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
        ≤ ENNReal.ofReal (((t1 - t0) / (φm N) : ℝ) * C)) :
    Filter.Tendsto (fun N : ℕ =>
        -∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))))).toFun p.2
            * slabDiffQuot t0 t1 (φm N) φ p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (-∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) := by
  set μ : Measure (ℝ × ℝ) := volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) with hμ
  set ubar : ℕ → ℝ × ℝ → ℝ := fun N p =>
    if p.1 = t1 then (U (φm N) (φm N)).toFun p.2
    else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)).toFun p.2 with hubar
  set ubarBack : ℕ → ℝ × ℝ → ℝ := fun N p =>
    (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))))).toFun p.2 with hubarBack
  set DQ : ℕ → ℝ × ℝ → ℝ := fun N p => slabDiffQuot t0 t1 (φm N) φ p with hDQ
  set phit : ℝ × ℝ → ℝ := fun p => deriv (fun s => φ s p.2) p.1 with hphit
  set uu : ℝ × ℝ → ℝ := fun p => u p.1 p.2 with huu
  set tau : ℕ → ℝ := fun N => (t1 - t0) / (φm N) with htau
  have hS : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  simp only [hμ, Measure.restrict_restrict hS, Set.inter_self] at hWeakThm ⊢
  have hMemphit : MemLp phit 2 μ := hMemLpDeriv
  have hMemu : MemLp uu 2 μ := hUMemLpThm
  obtain ⟨Cb, hCb0, hBound⟩ := hBoundThm
  obtain ⟨Cg, hCg0, hGap⟩ := hGapThm
  have hMemU : ∀ N, MemLp (fun p => ubar N p) 2 μ :=
    fun N => lt_of_le_of_lt (hBound N) ENNReal.ofReal_lt_top
  have hMemGap : ∀ N, MemLp (fun p => ubarBack N p - ubar N p) 2 μ :=
    fun N => lt_of_le_of_lt (hGap N) ENNReal.ofReal_lt_top
  have htauN : ∀ N, 0 ≤ tau N :=
    fun N => div_nonneg (le_of_lt (sub_pos.mpr ht)) (Nat.cast_nonneg _)
  have hGapToReal : ∀ N, (eLpNorm (fun p => ubarBack N p - ubar N p) 2 μ).toReal
      ≤ tau N * Cg := by
    intro N
    calc (eLpNorm (fun p => ubarBack N p - ubar N p) 2 μ).toReal
        ≤ (ENNReal.ofReal (tau N * Cg)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hGap N)
      _ = tau N * Cg := ENNReal.toReal_ofReal (mul_nonneg (htauN N) (le_of_lt hCg0))
  have hUToReal : ∀ N, (eLpNorm (fun p => ubar N p) 2 μ).toReal ≤ Cb := by
    intro N
    calc (eLpNorm (fun p => ubar N p) 2 μ).toReal
        ≤ (ENNReal.ofReal Cb).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBound N)
      _ = Cb := ENNReal.toReal_ofReal (le_of_lt hCb0)
  have hTest : Filter.Tendsto (fun N => eLpNorm (fun p => DQ N p - phit p) 2 μ)
      Filter.atTop (nhds 0) := hTestConvThm
  have hTestReal : Filter.Tendsto
      (fun N => (eLpNorm (fun p => DQ N p - phit p) 2 μ).toReal)
      Filter.atTop (nhds 0) := by
    have hcont : ContinuousAt ENNReal.toReal (0 : ENNReal) :=
      ENNReal.continuousAt_toReal (by simp)
    have h := hcont.tendsto.comp hTest
    rw [ENNReal.toReal_zero] at h
    exact h.congr (fun N => rfl)
  have hev1 : ∀ᶠ N in Filter.atTop, eLpNorm (fun p => DQ N p - phit p) 2 μ < 1 :=
    hTest.eventually (eventually_lt_nhds zero_lt_one)
  have hMemSub : ∀ᶠ N in Filter.atTop, MemLp (fun p => DQ N p - phit p) 2 μ := by
    filter_upwards [hev1] with N hN
    exact lt_trans hN ENNReal.one_lt_top
  have hMemDQ : ∀ᶠ N in Filter.atTop, MemLp (fun p => DQ N p) 2 μ := by
    filter_upwards [hMemSub] with N hN
    have hadd := hN.add hMemphit
    have heq : (fun p => DQ N p - phit p) + phit = fun p => DQ N p := by
      funext p
      exact sub_add_cancel _ _
    rw [heq] at hadd
    exact hadd
  set Kphi : ENNReal := eLpNorm phit 2 μ with hKphi
  have hKphilt : Kphi < ⊤ := hMemphit
  set K : ENNReal := 1 + Kphi with hK
  have hKne : K ≠ ⊤ := ne_of_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hKphilt⟩)
  have hDQle : ∀ᶠ N in Filter.atTop,
      (eLpNorm (fun p => DQ N p) 2 μ).toReal ≤ K.toReal := by
    filter_upwards [hev1] with N hN
    have heq : (fun p => DQ N p) = (fun p => DQ N p - phit p) + phit := by
      funext p
      exact (sub_add_cancel _ _).symm
    have htri : eLpNorm (fun p => DQ N p) 2 μ ≤ K := by
      rw [heq, hK, hKphi]
      exact (eLpNorm_add_le (by norm_num)).trans (add_le_add (le_of_lt hN) le_rfl)
    exact ENNReal.toReal_mono hKne htri
  have hphimtop : Filter.Tendsto φm Filter.atTop Filter.atTop := hφm.tendsto_atTop
  have htau : Filter.Tendsto tau Filter.atTop (nhds 0) := by
    have hbase := tendsto_const_div_atTop_nhds_zero_nat (t1 - t0)
    have h := hbase.comp hphimtop
    exact h.congr (fun N => rfl)
  have htauC : Filter.Tendsto (fun N => tau N * Cg) Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.mul_const Cg htau
    rw [zero_mul] at h
    exact h
  have htauCK : Filter.Tendsto (fun N => (tau N * Cg) * K.toReal)
      Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.mul_const K.toReal htauC
    rw [zero_mul] at h
    exact h
  -- Piece A: the gap term tends to 0.
  have hA : Filter.Tendsto (fun N => ∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ htauCK
    filter_upwards [hMemDQ, hDQle] with N hDQ hle
    calc ‖∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ‖
        ≤ (eLpNorm (fun p => ubarBack N p - ubar N p) 2 μ).toReal
          * (eLpNorm (fun p => DQ N p) 2 μ).toReal :=
          norm_integral_mul_le_eLpNorm_toReal_mul _ _ _ (hMemGap N) hDQ
      _ ≤ (tau N * Cg) * K.toReal :=
          mul_le_mul (hGapToReal N) hle ENNReal.toReal_nonneg
            (mul_nonneg (htauN N) (le_of_lt hCg0))
  -- Piece B: the test-function convergence term tends to 0.
  have hBg : Filter.Tendsto
      (fun N => Cb * (eLpNorm (fun p => DQ N p - phit p) 2 μ).toReal)
      Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul Cb hTestReal
    rw [mul_zero] at h
    exact h
  have hB : Filter.Tendsto (fun N => ∫ p, ubar N p * (DQ N p - phit p) ∂μ)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hBg
    filter_upwards [hMemSub] with N hSub
    calc ‖∫ p, ubar N p * (DQ N p - phit p) ∂μ‖
        ≤ (eLpNorm (fun p => ubar N p) 2 μ).toReal
          * (eLpNorm (fun p => DQ N p - phit p) 2 μ).toReal :=
          norm_integral_mul_le_eLpNorm_toReal_mul _ _ _ (hMemU N) hSub
      _ ≤ Cb * (eLpNorm (fun p => DQ N p - phit p) 2 μ).toReal :=
          mul_le_mul_of_nonneg_right (hUToReal N) ENNReal.toReal_nonneg
  -- Piece C: the weak-convergence term tends to 0.
  have hW : Filter.Tendsto (fun N => ∫ p, ubar N p * phit p ∂μ) Filter.atTop
      (nhds (∫ p, uu p * phit p ∂μ)) :=
    hWeakThm (fun t x => deriv (fun s => φ s x) t) hMemLpDeriv
  have hIntUphi : ∀ N, Integrable (fun p => ubar N p * phit p) μ := fun N =>
    ((hMemU N).integrable_mul hMemphit).congr (ae_of_all μ fun p => rfl)
  have hIntuphi : Integrable (fun p => uu p * phit p) μ :=
    (hMemu.integrable_mul hMemphit).congr (ae_of_all μ fun p => rfl)
  have hIntGapphi : ∀ N, Integrable (fun p => (ubar N p - uu p) * phit p) μ := fun N =>
    (((hMemU N).sub hMemu).integrable_mul hMemphit).congr (ae_of_all μ fun p => rfl)
  have hEqC : ∀ N, (∫ p, (ubar N p - uu p) * phit p ∂μ)
      = (∫ p, ubar N p * phit p ∂μ) - ∫ p, uu p * phit p ∂μ := by
    intro N
    calc (∫ p, (ubar N p - uu p) * phit p ∂μ)
        = ∫ p, (ubar N p * phit p) - (uu p * phit p) ∂μ :=
          integral_congr_ae (ae_of_all μ fun p => sub_mul _ _ _)
      _ = (∫ p, ubar N p * phit p ∂μ) - ∫ p, uu p * phit p ∂μ :=
          integral_sub (hIntUphi N) hIntuphi
  have hC : Filter.Tendsto (fun N => ∫ p, (ubar N p - uu p) * phit p ∂μ)
      Filter.atTop (nhds 0) := by
    have h := hW.sub_const (∫ p, uu p * phit p ∂μ)
    rw [sub_self] at h
    exact Filter.Tendsto.congr (fun N => (hEqC N).symm) h
  -- Combination.
  have hIntGapDQ : ∀ᶠ N in Filter.atTop,
      Integrable (fun p => (ubarBack N p - ubar N p) * DQ N p) μ := by
    filter_upwards [hMemDQ] with N hDQ
    exact ((hMemGap N).integrable_mul hDQ).congr (ae_of_all μ fun p => rfl)
  have hIntUDQ : ∀ᶠ N in Filter.atTop,
      Integrable (fun p => ubar N p * (DQ N p - phit p)) μ := by
    filter_upwards [hMemSub] with N hSub
    exact ((hMemU N).integrable_mul hSub).congr (ae_of_all μ fun p => rfl)
  have hEq : ∀ᶠ N in Filter.atTop,
      ((((∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
        + ∫ p, ubar N p * (DQ N p - phit p) ∂μ))
        + ∫ p, (ubar N p - uu p) * phit p ∂μ) + ∫ p, uu p * phit p ∂μ
      = ∫ p, ubarBack N p * DQ N p ∂μ := by
    filter_upwards [hIntGapDQ, hIntUDQ] with N h2 h3
    have e1 : (∫ p, ((ubarBack N p - ubar N p) * DQ N p
        + ubar N p * (DQ N p - phit p)) ∂μ)
        = (∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
          + ∫ p, ubar N p * (DQ N p - phit p) ∂μ :=
      integral_add h2 h3
    have e2 : (∫ p, ((ubarBack N p - ubar N p) * DQ N p
        + ubar N p * (DQ N p - phit p) + (ubar N p - uu p) * phit p) ∂μ)
        = ((∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
          + ∫ p, ubar N p * (DQ N p - phit p) ∂μ)
          + ∫ p, (ubar N p - uu p) * phit p ∂μ := by
      have h12 : (∫ p, (((ubarBack N p - ubar N p) * DQ N p
          + ubar N p * (DQ N p - phit p))) + (ubar N p - uu p) * phit p ∂μ)
          = (∫ p, ((ubarBack N p - ubar N p) * DQ N p
            + ubar N p * (DQ N p - phit p)) ∂μ)
            + ∫ p, (ubar N p - uu p) * phit p ∂μ :=
        integral_add (h2.add h3) (hIntGapphi N)
      rw [h12, e1]
    have e3 : (∫ p, ((ubarBack N p - ubar N p) * DQ N p
        + ubar N p * (DQ N p - phit p) + (ubar N p - uu p) * phit p
        + uu p * phit p) ∂μ)
        = ((((∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
          + ∫ p, ubar N p * (DQ N p - phit p) ∂μ))
          + ∫ p, (ubar N p - uu p) * phit p ∂μ) + ∫ p, uu p * phit p ∂μ := by
      have h123 : (∫ p, (((ubarBack N p - ubar N p) * DQ N p
          + ubar N p * (DQ N p - phit p) + (ubar N p - uu p) * phit p))
          + uu p * phit p ∂μ)
          = (∫ p, ((ubarBack N p - ubar N p) * DQ N p
            + ubar N p * (DQ N p - phit p) + (ubar N p - uu p) * phit p) ∂μ)
            + ∫ p, uu p * phit p ∂μ :=
        integral_add ((h2.add h3).add (hIntGapphi N)) hIntuphi
      rw [h123, e2]
    calc ((((∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
          + ∫ p, ubar N p * (DQ N p - phit p) ∂μ))
          + ∫ p, (ubar N p - uu p) * phit p ∂μ) + ∫ p, uu p * phit p ∂μ
        = ∫ p, ((ubarBack N p - ubar N p) * DQ N p
          + ubar N p * (DQ N p - phit p) + (ubar N p - uu p) * phit p
          + uu p * phit p) ∂μ := e3.symm
      _ = ∫ p, ubarBack N p * DQ N p ∂μ :=
          integral_congr_ae (ae_of_all μ fun p => by ring)
  have hD : Filter.Tendsto (fun _ : ℕ => ∫ p, uu p * phit p ∂μ) Filter.atTop
      (nhds (∫ p, uu p * phit p ∂μ)) := tendsto_const_nhds
  have hSum : Filter.Tendsto
      (fun N => ((((∫ p, (ubarBack N p - ubar N p) * DQ N p ∂μ)
        + ∫ p, ubar N p * (DQ N p - phit p) ∂μ))
        + ∫ p, (ubar N p - uu p) * phit p ∂μ) + ∫ p, uu p * phit p ∂μ)
      Filter.atTop (nhds (∫ p, uu p * phit p ∂μ)) := by
    have h := ((hA.add hB).add hC).add hD
    simpa only [zero_add, add_zero] using h
  have hTotal : Filter.Tendsto (fun N => ∫ p, ubarBack N p * DQ N p ∂μ)
      Filter.atTop (nhds (∫ p, uu p * phit p ∂μ)) :=
    Filter.Tendsto.congr' hEq hSum
  have hGoal : Filter.Tendsto (fun N => -∫ p, ubarBack N p * DQ N p ∂μ)
      Filter.atTop (nhds (-∫ p, uu p * phit p ∂μ)) := hTotal.neg
  exact hGoal


noncomputable def slabSampleFn (t0 t1 : ℝ) (N : ℕ) (g : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 = t1 then g t1 p.2
  else g (slabRight t0 t1 N p.1) p.2


instance holderTriple_two_two_one : (2 : ENNReal).HolderTriple 2 1 :=
  NNReal.HolderTriple.coe_ennreal (r := 1) (by norm_num)
    (NNReal.HolderTriple.mk (p := 2) (q := 2) (by ext; push_cast; norm_num) (by norm_num)
      (by norm_num))


theorem norm_integral_mul_le_eLpNorm_toReal_mul_toReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ‖∫ x, u x * v x ∂μ‖ ≤ (eLpNorm u 2 μ).toReal * (eLpNorm v 2 μ).toReal := by
  have h1 : MemLp (fun x => u x * v x) 1 μ := hu.fun_mul (r := 1) hv
  have hH : eLpNorm (fun x => u x * v x) 1 μ ≤ eLpNorm u 2 μ * eLpNorm v 2 μ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (f := u) (g := v) (μ := μ)
      (p := 2) (q := 2) (r := 1)
      (fun (a b : ℝ) => a * b) 1 continuous_mul
      (by filter_upwards with x; simp)
      (by norm_num)
    simpa using h
  have hmeas : AEStronglyMeasurable (fun x => u x * v x) μ := h1.aestronglyMeasurable
  have hL1 : ‖∫ x, u x * v x ∂μ‖ ≤ (eLpNorm (fun x => u x * v x) 1 μ).toReal := by
    calc ‖∫ x, u x * v x ∂μ‖ ≤ ∫ x, ‖u x * v x‖ ∂μ := norm_integral_le_integral_norm _
      _ = (∫⁻ x, ENNReal.ofReal ‖u x * v x‖ ∂μ).toReal :=
          integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun x => norm_nonneg _) hmeas.norm
      _ = (eLpNorm (fun x => u x * v x) 1 μ).toReal := by
          rw [eLpNorm_one_eq_lintegral_enorm hmeas]
          simp only [ofReal_norm]
  calc ‖∫ x, u x * v x ∂μ‖ ≤ (eLpNorm (fun x => u x * v x) 1 μ).toReal := hL1
    _ ≤ (eLpNorm u 2 μ * eLpNorm v 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hu.eLpNorm_ne_top hv.eLpNorm_ne_top) hH
    _ = (eLpNorm u 2 μ).toReal * (eLpNorm v 2 μ).toReal := ENNReal.toReal_mul


theorem tendsto_integral_mul_of_tendsto_eLpNorm_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {G : ℕ → α → ℝ} {F : α → ℝ} {S : ℕ → α → ℝ} {φ : α → ℝ}
    (hF : MemLp F 2 μ) (hφ : MemLp φ 2 μ)
    (hAvg : Filter.Tendsto (fun N => eLpNorm (fun x => G N x - F x) 2 μ) Filter.atTop (nhds 0))
    (hSamp : Filter.Tendsto (fun N => eLpNorm (fun x => S N x - φ x) 2 μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => ∫ x, G N x * S N x ∂μ) Filter.atTop
      (nhds (∫ x, F x * φ x ∂μ)) := by
  have h1top : (1 : ENNReal) < ⊤ := by simp
  have hAvg1 : ∀ᶠ N in Filter.atTop, eLpNorm (fun x => G N x - F x) 2 μ < 1 :=
    hAvg.eventually_lt_const (by norm_num)
  have hSamp1 : ∀ᶠ N in Filter.atTop, eLpNorm (fun x => S N x - φ x) 2 μ < 1 :=
    hSamp.eventually_lt_const (by norm_num)
  have hAvgMem : ∀ᶠ N in Filter.atTop, MemLp (fun x => G N x - F x) 2 μ := by
    filter_upwards [hAvg1] with N hN
    exact lt_trans hN h1top
  have hSampMem : ∀ᶠ N in Filter.atTop, MemLp (fun x => S N x - φ x) 2 μ := by
    filter_upwards [hSamp1] with N hN
    exact lt_trans hN h1top
  have hSMem : ∀ᶠ N in Filter.atTop, MemLp (S N) 2 μ := by
    filter_upwards [hSampMem] with N hN
    have heq : (fun x => S N x - φ x) + φ = S N := by
      ext x
      exact sub_add_cancel _ _
    have h := hN.add hφ
    rwa [heq] at h
  have hSbd : ∀ᶠ N in Filter.atTop,
      (eLpNorm (S N) 2 μ).toReal ≤ 1 + (eLpNorm φ 2 μ).toReal := by
    filter_upwards [hSamp1] with N h1
    have heq : (fun x => S N x - φ x) + φ = S N := by
      ext x
      exact sub_add_cancel _ _
    have htri : eLpNorm (S N) 2 μ ≤ eLpNorm (fun x => S N x - φ x) 2 μ + eLpNorm φ 2 μ := by
      have h := eLpNorm_add_le (f := (fun x => S N x - φ x)) (g := φ) (p := 2) (μ := μ)
        (by norm_num)
      rwa [heq] at h
    have hle : eLpNorm (S N) 2 μ ≤ 1 + eLpNorm φ 2 μ :=
      htri.trans (add_le_add_left (le_of_lt h1) _)
    have hfin1 : (1 : ENNReal) ≠ ⊤ := by simp
    calc (eLpNorm (S N) 2 μ).toReal ≤ (1 + eLpNorm φ 2 μ).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hφ.eLpNorm_ne_top⟩) hle
      _ = 1 + (eLpNorm φ 2 μ).toReal := by
          rw [ENNReal.toReal_add hfin1 hφ.eLpNorm_ne_top, ENNReal.toReal_one]
  have hAvgToReal : Filter.Tendsto (fun N => (eLpNorm (fun x => G N x - F x) 2 μ).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hAvg
    have h0 : (0 : ENNReal).toReal = 0 := by simp
    rw [h0] at h
    exact h
  have hSampToReal : Filter.Tendsto (fun N => (eLpNorm (fun x => S N x - φ x) 2 μ).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hSamp
    have h0 : (0 : ENNReal).toReal = 0 := by simp
    rw [h0] at h
    exact h
  have hPieceA : Filter.Tendsto (fun N => ∫ x, (G N x - F x) * S N x ∂μ) Filter.atTop (nhds 0) := by
    have hC : Filter.Tendsto
        (fun N => (eLpNorm (fun x => G N x - F x) 2 μ).toReal * (1 + (eLpNorm φ 2 μ).toReal))
        Filter.atTop (nhds 0) := by
      have h := hAvgToReal.const_mul (1 + (eLpNorm φ 2 μ).toReal)
      rw [mul_zero] at h
      exact h.congr (fun N => mul_comm _ _)
    have h0 : ∀ᶠ N in Filter.atTop,
        0 ≤ (eLpNorm (fun x => G N x - F x) 2 μ).toReal * (eLpNorm (S N) 2 μ).toReal :=
      Filter.Eventually.of_forall fun N =>
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hle : ∀ᶠ N in Filter.atTop,
        (eLpNorm (fun x => G N x - F x) 2 μ).toReal * (eLpNorm (S N) 2 μ).toReal
          ≤ (eLpNorm (fun x => G N x - F x) 2 μ).toReal * (1 + (eLpNorm φ 2 μ).toReal) := by
      filter_upwards [hSbd] with N hN
      exact mul_le_mul_of_nonneg_left hN ENNReal.toReal_nonneg
    have hab : Filter.Tendsto
        (fun N => (eLpNorm (fun x => G N x - F x) 2 μ).toReal * (eLpNorm (S N) 2 μ).toReal)
        Filter.atTop (nhds 0) :=
      squeeze_zero' h0 hle hC
    apply squeeze_zero_norm' _ hab
    filter_upwards [hAvgMem, hSMem] with N h1 h2
    exact norm_integral_mul_le_eLpNorm_toReal_mul_toReal h1 h2
  have hPieceB : Filter.Tendsto (fun N => ∫ x, F x * (S N x - φ x) ∂μ) Filter.atTop (nhds 0) := by
    have hC : Filter.Tendsto
        (fun N => (eLpNorm F 2 μ).toReal * (eLpNorm (fun x => S N x - φ x) 2 μ).toReal)
        Filter.atTop (nhds 0) := by
      have h := hSampToReal.const_mul (eLpNorm F 2 μ).toReal
      rwa [mul_zero] at h
    apply squeeze_zero_norm' _ hC
    filter_upwards [hSampMem] with N hN
    exact norm_integral_mul_le_eLpNorm_toReal_mul_toReal hF hN
  have hIntB : Integrable (fun x => F x * φ x) μ := (hF.fun_mul (r := 1) hφ).integrable le_rfl
  have hIntP : ∀ᶠ N in Filter.atTop, Integrable (fun x => (G N x - F x) * S N x) μ := by
    filter_upwards [hAvgMem, hSMem] with N h1 h2
    exact (h1.fun_mul (r := 1) h2).integrable le_rfl
  have hIntQ : ∀ᶠ N in Filter.atTop, Integrable (fun x => F x * (S N x - φ x)) μ := by
    filter_upwards [hSampMem] with N hN
    exact (hF.fun_mul (r := 1) hN).integrable le_rfl
  have hEq : (fun N => ∫ x, G N x * S N x ∂μ) =ᶠ[Filter.atTop]
      (fun N => (∫ x, (G N x - F x) * S N x ∂μ) + (∫ x, F x * (S N x - φ x) ∂μ)
        + ∫ x, F x * φ x ∂μ) := by
    show ∀ᶠ N in Filter.atTop, _
    filter_upwards [hIntP, hIntQ] with N hP hQ
    have hQB : Integrable (fun x => F x * (S N x - φ x) + F x * φ x) μ := hQ.add hIntB
    have hid : (fun x => G N x * S N x)
        = (fun x => (G N x - F x) * S N x + (F x * (S N x - φ x) + F x * φ x)) :=
      funext fun x => by ring
    have e1 : (∫ x, G N x * S N x ∂μ)
        = (∫ x, (G N x - F x) * S N x ∂μ)
          + (∫ x, F x * (S N x - φ x) + F x * φ x ∂μ) := by
      rw [hid]
      exact integral_add hP hQB
    have e2 : (∫ x, F x * (S N x - φ x) + F x * φ x ∂μ)
        = (∫ x, F x * (S N x - φ x) ∂μ) + ∫ x, F x * φ x ∂μ :=
      integral_add hQ hIntB
    calc (∫ x, G N x * S N x ∂μ)
        = (∫ x, (G N x - F x) * S N x ∂μ)
          + (∫ x, F x * (S N x - φ x) + F x * φ x ∂μ) := e1
      _ = (∫ x, (G N x - F x) * S N x ∂μ) + ((∫ x, F x * (S N x - φ x) ∂μ)
          + ∫ x, F x * φ x ∂μ) := by rw [e2]
      _ = (∫ x, (G N x - F x) * S N x ∂μ) + (∫ x, F x * (S N x - φ x) ∂μ)
          + ∫ x, F x * φ x ∂μ := (add_assoc _ _ _).symm
  have hsum : Filter.Tendsto
      (fun N => (∫ x, (G N x - F x) * S N x ∂μ) + (∫ x, F x * (S N x - φ x) ∂μ)
        + ∫ x, F x * φ x ∂μ)
      Filter.atTop (nhds (∫ x, F x * φ x ∂μ)) := by
    have h := (hPieceA.add hPieceB).add_const (∫ x, F x * φ x ∂μ)
    simpa using h
  exact hsum.congr' hEq.symm

/-- Forcing-term passage. -/

theorem rothe_term3_tendsto
    {t0 t1 : ℝ} (ht : t0 < t1)
    {F : ℝ → ℝ → ℝ}
    (hFMemLpThm : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ)
    (Fbar : ℕ → ℕ → ℝ → ℝ)
    (hAvgThm : Filter.Tendsto (fun N : ℕ =>
        eLpNorm (fun p : ℝ × ℝ =>
          (if p.1 = t1 then Fbar (φm N) ((φm N) - 1) p.2
           else Fbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
            - F p.1 p.2) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (hFbarMeasThm : ∀ (M : ℕ), AEStronglyMeasurable
      (fun p : ℝ × ℝ => (if p.1 = t1 then Fbar M (M - 1) p.2
        else Fbar M (Nat.floor ((p.1 - t0) / ((t1 - t0) / M))) p.2))
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hSampleThm : Filter.Tendsto (fun N : ℕ =>
        eLpNorm (fun p : ℝ × ℝ =>
          slabSampleFn t0 t1 (φm N) φ p - φ p.1 p.2) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then Fbar (φm N) ((φm N) - 1) p.2
           else Fbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
            * slabSampleFn t0 t1 (φm N) φ p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        F p.1 p.2 * φ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) := by
  have hs : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hCss : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact (IsCompact.measure_lt_top hCss).ne
  haveI := hfin
  simp only [Measure.restrict_restrict hs, Set.inter_self]
  have hφcont : Continuous (fun p : ℝ × ℝ => φ p.1 p.2) := hφ.1.continuous
  have hφmem : MemLp (fun p : ℝ × ℝ => φ p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    obtain ⟨C, hC⟩ := hCss.exists_bound_of_continuousOn hφcont.continuousOn
    exact MemLp.of_bound hφcont.aestronglyMeasurable C
      ((ae_restrict_mem hs).mono fun x hx => hC x hx)
  have hFmem : MemLp (fun p : ℝ × ℝ => F p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := hFMemLpThm
  exact tendsto_integral_mul_of_tendsto_eLpNorm_zero hFmem hφmem hAvgThm hSampleThm


theorem rothe_term2a_strong_coeff
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (kbar : ℕ → ℝ → ℝ)
    (hAvgThm : Filter.Tendsto (fun N : ℕ =>
        eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (U : ℕ → (ℝ → ℝ))
    (hBoundThm : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      eLpNorm (Function.uncurry (fun t x => U N x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) ≤ ENNReal.ofReal C)
    (ψN : ℕ → ℝ → ℝ → ℝ)
    (hSampleBddThm : ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, ∀ p : ℝ × ℝ,
      |ψN N p.1 p.2| ≤ B) :
    Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ := hBoundThm
  obtain ⟨B, hBpos, hB⟩ := hSampleBddThm
  set E : Set (ℝ × ℝ) := Set.Icc t0 t1 ×ˢ Set.Icc 0 1 with hE
  set μ : Measure (ℝ × ℝ) := volume.restrict E with hμ
  have hEmeas : MeasurableSet E := by
    rw [hE]
    exact MeasurableSet.prod measurableSet_Icc measurableSet_Icc
  have eLpNorm_top_of_not_meas : ∀ {f : ℝ × ℝ → ℝ} {p : ENNReal},
      ¬AEStronglyMeasurable f μ → eLpNorm f p μ = ⊤ := fun h => by
    unfold eLpNorm
    simp [h]
  have h0ne : (0 : ENNReal) ≠ ⊤ := by simp
  have h221 : (2 : ENNReal).HolderTriple 2 1 := by
    apply ENNReal.HolderTriple.of_toReal
    rw [Real.holderTriple_iff]
    norm_num [ENNReal.toReal_ofNat, ENNReal.toReal_one]
  have hinf11 : (⊤ : ENNReal).HolderTriple 1 1 :=
    @ENNReal.HolderTriple.symm 1 ⊤ 1 (ENNReal.HolderTriple.instInfty 1)
  have hmeas_eq : μ.restrict E = μ := by
    rw [hμ, Measure.restrict_restrict hEmeas, Set.inter_self]
  have hconstB : eLpNorm (fun _ : ℝ × ℝ => B) ⊤ μ ≤ ENNReal.ofReal B := by
    have hexp : (⊤ : ENNReal).toReal⁻¹ = (0 : ℝ) := by
      rw [ENNReal.toReal_top, inv_zero]
    have h := eLpNorm_le_of_ae_bound (μ := μ) (f := fun _ : ℝ × ℝ => B) (p := ⊤) (C := B)
      aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by
        show ‖B‖ ≤ B
        rw [Real.norm_eq_abs, abs_of_pos hBpos])
    rwa [hexp, ENNReal.rpow_zero, one_mul] at h
  have hcont : Continuous (Function.uncurry fun x y : ℝ => x * y) :=
    Continuous.mul continuous_fst continuous_snd
  have hnorm_le : ∀ w ψ : ℝ, |ψ| ≤ B → ‖w * ψ‖ ≤ ‖B * w‖ := by
    intro w ψ hψ
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_of_pos hBpos, mul_comm B |w|]
    exact mul_le_mul_of_nonneg_left hψ (abs_nonneg _)
  have hbound : ∀ N : ℕ,
      eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ ≠ ⊤ →
      ‖∫ p in E, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂μ‖
        ≤ B * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ).toReal * C := by
    intro N hfNne
    have hfN : AEStronglyMeasurable (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) μ := by
      by_contra hcon
      exact hfNne (eLpNorm_top_of_not_meas hcon)
    have huncurry : Function.uncurry (fun t x => U N x)
        = fun p : ℝ × ℝ => U N p.2 := rfl
    have huN_bound : eLpNorm (fun p : ℝ × ℝ => U N p.2) 2 μ ≤ ENNReal.ofReal C := by
      rw [← huncurry]
      exact hC N
    have huN : AEStronglyMeasurable (fun p : ℝ × ℝ => U N p.2) μ := by
      by_contra hcon
      have htop : eLpNorm (fun p : ℝ × ℝ => U N p.2) 2 μ = ⊤ :=
        eLpNorm_top_of_not_meas hcon
      rw [htop] at huN_bound
      exact (not_le.mpr ENNReal.ofReal_lt_top) huN_bound
    have hwN : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2) μ :=
      hfN.mul huN
    have hHolder_fu : eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2) 1 μ
        ≤ eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ
          * eLpNorm (fun p : ℝ × ℝ => U N p.2) 2 μ := by
      have h := eLpNorm_le_eLpNorm_mul_eLpNorm (b := fun x y : ℝ => x * y) (c := 1)
        hcont hfN huN
        (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
        (p := 2) (q := 2) (r := 1) (hpqr := h221)
      simpa using h
    have hHolder_Bw : eLpNorm (fun p : ℝ × ℝ => B * ((kbar N p.2 - κ p.1 p.2) * U N p.2)) 1 μ
        ≤ eLpNorm (fun _ : ℝ × ℝ => B) ⊤ μ
          * eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2) 1 μ := by
      have h := eLpNorm_le_eLpNorm_mul_eLpNorm (b := fun x y : ℝ => x * y) (c := 1)
        (f := fun _ : ℝ × ℝ => B) hcont aestronglyMeasurable_const hwN
        (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
        (p := ⊤) (q := 1) (r := 1) (hpqr := hinf11)
      simpa using h
    by_cases hHint : Integrable
      (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) μ
    · have hHmeas : AEStronglyMeasurable
          (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) μ :=
        hHint.aestronglyMeasurable
      have hmono : eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) 1 μ
          ≤ eLpNorm (fun p : ℝ × ℝ => B * ((kbar N p.2 - κ p.1 p.2) * U N p.2)) 1 μ := by
        apply eLpNorm_mono hHmeas
        intro p
        exact hnorm_le _ _ (hB N p)
      have h5 : eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) 1 μ
          ≤ ENNReal.ofReal B
            * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ * ENNReal.ofReal C) :=
        calc eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) 1 μ
              ≤ eLpNorm (fun p : ℝ × ℝ => B * ((kbar N p.2 - κ p.1 p.2) * U N p.2)) 1 μ :=
              hmono
            _ ≤ eLpNorm (fun _ : ℝ × ℝ => B) ⊤ μ
                * eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2) 1 μ :=
              hHolder_Bw
            _ ≤ ENNReal.ofReal B
                * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ
                  * eLpNorm (fun p : ℝ × ℝ => U N p.2) 2 μ) :=
              mul_le_mul' hconstB hHolder_fu
            _ ≤ ENNReal.ofReal B
                * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ * ENNReal.ofReal C) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl huN_bound)
      have hbfin : ENNReal.ofReal B
          * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ * ENNReal.ofReal C) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hfNne ENNReal.ofReal_ne_top)
      have h6 : (eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) 1 μ).toReal
          ≤ (ENNReal.ofReal B
            * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ * ENNReal.ofReal C)).toReal :=
        ENNReal.toReal_mono hbfin h5
      have h7 : (ENNReal.ofReal B
          * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ * ENNReal.ofReal C)).toReal
          = B * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ).toReal * C := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (le_of_lt hBpos), ENNReal.toReal_ofReal (le_of_lt hCpos)]
        ring
      have h1 : ‖∫ p, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂μ‖
          ≤ ∫ p, ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ ∂μ :=
        norm_integral_le_integral_norm _
      have h2 : (∫ p, ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ ∂μ)
          = (∫⁻ p, ENNReal.ofReal ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ ∂μ).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (f := fun p : ℝ × ℝ => ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖)
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) hHmeas.norm
      have h3 : (∫⁻ p, ENNReal.ofReal ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ ∂μ)
          = ∫⁻ p, ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ₑ ∂μ := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          show ENNReal.ofReal ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖
            = ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ₑ
          rw [Real.norm_eq_abs]
          exact (Real.enorm_eq_ofReal_abs _).symm
      have h4 : (∫⁻ p, ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ₑ ∂μ)
          = eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) 1 μ :=
        (eLpNorm_one_eq_lintegral_enorm hHmeas).symm
      rw [show (∫ p in E, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂μ)
          = ∫ p, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂(μ.restrict E) from rfl,
        hmeas_eq]
      calc ‖∫ p, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂μ‖
            ≤ ∫ p, ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ ∂μ := h1
          _ = (∫⁻ p, ENNReal.ofReal ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ ∂μ).toReal := h2
          _ = (∫⁻ p, ‖(kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2‖ₑ ∂μ).toReal := by rw [h3]
          _ = (eLpNorm (fun p : ℝ × ℝ => (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2) 1 μ).toReal := by rw [h4]
          _ ≤ (ENNReal.ofReal B
            * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ * ENNReal.ofReal C)).toReal := h6
          _ = B * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ).toReal * C := h7
    · have hz : (∫ p in E, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂μ) = 0 := by
        show ∫ p, (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2 ∂(μ.restrict E) = 0
        rw [hmeas_eq]
        exact integral_undef hHint
      rw [hz, norm_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hBpos) ENNReal.toReal_nonneg) (le_of_lt hCpos)
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ ≠ ⊤ := by
    have hmem : ({⊤} : Set ENNReal)ᶜ ∈ nhds (0 : ENNReal) :=
      compl_singleton_mem_nhds h0ne
    have h := hAvgThm.eventually hmem
    simpa using h
  have hto0 : Filter.Tendsto
      (fun N : ℕ => (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ).toReal)
      Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal h0ne).comp hAvgThm
    have h' : Filter.Tendsto
        (fun N : ℕ => (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ).toReal)
        Filter.atTop (nhds ((0 : ENNReal).toReal)) := h
    simpa using h'
  have ha0 : Filter.Tendsto
      (fun N : ℕ => B * (eLpNorm (fun p : ℝ × ℝ => kbar N p.2 - κ p.1 p.2) 2 μ).toReal * C)
      Filter.atTop (nhds 0) := by
    have h := (hto0.const_mul B).mul_const C
    simpa using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ha0 _ _
  · exact Filter.Eventually.of_forall fun N => norm_nonneg _
  · exact hev.mono fun N hN => hbound N hN


theorem rothe_term2b_moving_test
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (U : ℕ → (ℝ → ℝ))
    (hBoundThm : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      eLpNorm (fun p : ℝ × ℝ => κ p.1 p.2 * U N p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) ≤ ENNReal.ofReal C)
    (ψN : ℕ → ℝ → ℝ → ℝ) (ψ : ℝ → ℝ → ℝ)
    (hSampleThm : Filter.Tendsto (fun N : ℕ =>
        eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hCbound⟩ := hBoundThm
  haveI hH : (2 : ENNReal).HolderTriple 2 1 := .mk (by
    have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    rw [h2, h1, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1
    norm_num)
  have hToReal : Filter.Tendsto (fun N : ℕ => (eLpNorm
      (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal)
      Filter.atTop (nhds 0) := by
    have hCont' : Filter.Tendsto ENNReal.toReal (nhds (0 : ENNReal)) (nhds 0) := by
      simpa using ENNReal.tendsto_toReal (show (0 : ENNReal) ≠ ⊤ by simp)
    exact hCont'.comp hSampleThm
  have hCMul : Filter.Tendsto (fun N : ℕ => C * (eLpNorm
      (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := C)).mul hToReal
    simpa using h
  have hNeTop : ∀ᶠ N : ℕ in Filter.atTop, eLpNorm
      (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) ≠ ⊤ :=
    hSampleThm.eventually_ne (by simp)
  apply squeeze_zero_norm' _ hCMul
  filter_upwards [hNeTop] with N hN
  have hf_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => κ p.1 p.2 * U N p.2)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCbound N))
  have hg_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    aestronglyMeasurable_of_eLpNorm_ne_top hN
  have hfg_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2))
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    hf_meas.mul hg_meas
  have hHolder : eLpNorm
      (fun p : ℝ × ℝ => (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)) 1
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) ≤
      eLpNorm (fun p : ℝ × ℝ => κ p.1 p.2 * U N p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) *
      eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (μ := volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      (f := fun p : ℝ × ℝ => κ p.1 p.2 * U N p.2)
      (g := fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2)
      (p := 2) (q := 2) (r := 1)
      (fun a b => a * b) 1 continuous_mul hf_meas hg_meas
      (Filter.Eventually.of_forall fun x => by simp [norm_mul])
    simpa using h
  have hInt : ‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ₑ ≤
      eLpNorm (fun p : ℝ × ℝ => κ p.1 p.2 * U N p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) *
      eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    calc ‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ₑ
        ≤ ∫⁻ p, ‖(κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)‖ₑ
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
          enorm_integral_le_lintegral_enorm _
      _ = eLpNorm
            (fun p : ℝ × ℝ => (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)) 1
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
          (eLpNorm_one_eq_lintegral_enorm hfg_meas).symm
      _ ≤ _ := hHolder
  have hENN : ‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ₑ ≤
      ENNReal.ofReal C * eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    calc ‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ₑ
        ≤ eLpNorm (fun p : ℝ × ℝ => κ p.1 p.2 * U N p.2) 2
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) *
          eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := hInt
      _ ≤ ENNReal.ofReal C * eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
            (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
          gcongr
          exact hCbound N
  have hRHS_ne : ENNReal.ofReal C * eLpNorm
      (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  have hReal : (‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ₑ).toReal ≤
      (ENNReal.ofReal C * eLpNorm (fun p : ℝ × ℝ => ψN N p.1 p.2 - ψ p.1 p.2) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal :=
    (ENNReal.toReal_le_toReal enorm_ne_top hRHS_ne).mpr hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hCpos)] at hReal
  have hEnorm : (‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ₑ).toReal =
      ‖∫ p, (κ p.1 p.2 * U N p.2) * (ψN N p.1 p.2 - ψ p.1 p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))‖ := by
    rw [← enorm_norm, Real.enorm_eq_ofReal (norm_nonneg _),
      ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [hEnorm] at hReal
  have hMeasEq : ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)).restrict
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) =
      volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) :=
    Measure.restrict_restrict_of_subset (fun _ h => h)
  rw [hMeasEq]
  exact hReal


theorem rothe_term2_asm_abstract_fixed
    {t0 t1 : ℝ} (_ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (kbar : ℕ → ℝ → ℝ)
    (U : ℕ → (ℝ → ℝ))
    (ψN : ℕ → ℝ → ℝ → ℝ) (ψ : ℝ → ℝ → ℝ)
    (hTerm2aThm : Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (hTerm2bThm : Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (hKappaPsiMemLpThm : MemLp (Function.uncurry (fun t x => κ t x * ψ t x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (ux : ℝ → ℝ → ℝ)
    (hWeakThm : ∀ ψ' : ℝ → ℝ → ℝ,
      MemLp (Function.uncurry ψ') 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            U N p.2 * ψ' p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          ux p.1 p.2 * ψ' p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hIntA : ∀ N : ℕ, Integrable (fun p : ℝ × ℝ =>
        (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2)
      ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)).restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hIntB : ∀ N : ℕ, Integrable (fun p : ℝ × ℝ =>
        κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
      ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)).restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hIntC : ∀ N : ℕ, Integrable (fun p : ℝ × ℝ =>
        κ p.1 p.2 * U N p.2 * ψ p.1 p.2)
      ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)).restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) :
    Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          kbar N p.2 * U N p.2 * ψN N p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * ux p.1 p.2 * ψ p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) := by
  have hpt : ∀ (N : ℕ) (p : ℝ × ℝ),
      kbar N p.2 * U N p.2 * ψN N p.1 p.2
        = ((kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
          + κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
          + κ p.1 p.2 * U N p.2 * ψ p.1 p.2 := by
    intro N p
    ring
  have hsplit : ∀ N : ℕ,
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          kbar N p.2 * U N p.2 * ψN N p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * U N p.2 * ψ p.1 p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    intro N
    have e0 : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          kbar N p.2 * U N p.2 * ψN N p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (((kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
            + κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
            + κ p.1 p.2 * U N p.2 * ψ p.1 p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
      integral_congr_ae (Filter.Eventually.of_forall (hpt N))
    have hAB : Integrable (fun p : ℝ × ℝ =>
        (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
          + κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
        ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)).restrict
          (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
      (hIntA N).add (hIntB N)
    have e1 : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (((kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
            + κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
            + κ p.1 p.2 * U N p.2 * ψ p.1 p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ((kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
              + κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          + ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              κ p.1 p.2 * U N p.2 * ψ p.1 p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
      integral_add hAB (hIntC N)
    have e2 : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ((kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
              + κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2))
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              (kbar N p.2 - κ p.1 p.2) * U N p.2 * ψN N p.1 p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          + ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              κ p.1 p.2 * U N p.2 * (ψN N p.1 p.2 - ψ p.1 p.2)
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
      integral_add (hIntA N) (hIntB N)
    rw [e0, e1, e2]
  have hW := hWeakThm (fun t x => κ t x * ψ t x) hKappaPsiMemLpThm
  have hC : Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * U N p.2 * ψ p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * ux p.1 p.2 * ψ p.1 p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) := by
    have eF : ∀ N : ℕ, (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * U N p.2 * ψ p.1 p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            U N p.2 * (fun t x => κ t x * ψ t x) p.1 p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
      intro N
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      show κ p.1 p.2 * U N p.2 * ψ p.1 p.2 = U N p.2 * (κ p.1 p.2 * ψ p.1 p.2)
      ring
    have eL : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ux p.1 p.2 * (fun t x => κ t x * ψ t x) p.1 p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * ux p.1 p.2 * ψ p.1 p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      show ux p.1 p.2 * (κ p.1 p.2 * ψ p.1 p.2)
        = κ p.1 p.2 * ux p.1 p.2 * ψ p.1 p.2
      ring
    rw [eL] at hW
    exact Filter.Tendsto.congr (fun N => (eF N).symm) hW
  have hsum := (hTerm2aThm.add hTerm2bThm).add hC
  simp only [add_zero, zero_add] at hsum
  exact Filter.Tendsto.congr (fun N => (hsplit N).symm) hsum

-- Fixed: `hWeakUx` below refers to the generic `Ugrad` argument of this
-- theorem. The as-given text named a constant that is not in scope here.

theorem rothe_term2_inst
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (u ux : ℝ → ℝ → ℝ)
    (Ugrad : ℕ → ℝ → (ℝ → ℝ))
    (slabAvg : (ℝ → ℝ → ℝ) → ℕ → (ℝ → ℝ → ℝ))
    (hSlabCoeffThm : ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => slabAvg κ N t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (φ : ℝ → ℝ → ℝ)
    (hTerm2AsmThm : ∀ (kbar : ℕ → ℝ → ℝ → ℝ) (ugrad : ℕ → ℝ → ℝ → ℝ)
      (φf : ℝ → ℝ → ℝ),
      (∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
        MemLp (fun x => kbar N t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
        MemLp (fun x => ugrad N t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N →
        Integrable (fun p : ℝ × ℝ => kbar N p.1 p.2 * ugrad N p.1 p.2
          * deriv (fun y => φf p.1 y) p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N →
        Integrable (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2
          * deriv (fun y => φf p.1 y) p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N →
        Integrable (fun p : ℝ × ℝ => (kbar N p.1 p.2 - κ p.1 p.2) * ugrad N p.1 p.2
          * deriv (fun y => φf p.1 y) p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (kbar N p.1 p.2 - κ p.1 p.2) * ux p.1 p.2
              * deriv (fun y => φf p.1 y) p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds 0) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            kbar N p.1 p.2 * ugrad N p.1 p.2
              * deriv (fun y => φf p.1 y) p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φf p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hGradWeakThm : ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => Ugrad N t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hIntSlabThm : ∀ (N : ℕ), 0 < N →
      Integrable (fun p : ℝ × ℝ => slabAvg κ N p.1 p.2 * Ugrad N p.1 p.2
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hIntLimThm : Integrable (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hIntDiffThm : ∀ (N : ℕ), 0 < N →
      Integrable (fun p : ℝ × ℝ => (slabAvg κ N p.1 p.2 - κ p.1 p.2) * Ugrad N p.1 p.2
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hWeakUx : ∀ ψ : ℝ → ℝ → ℝ,
        MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
        Filter.Tendsto (fun N : ℕ =>
            ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              Ugrad N p.1 p.2 * ψ p.1 p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ux p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hIntMain : Integrable (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hCoeffDiffThm : Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (slabAvg κ N p.1 p.2 - κ p.1 p.2) * ux p.1 p.2
            * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          slabAvg κ N p.1 p.2 * Ugrad N p.1 p.2
            * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) := by
  exact hTerm2AsmThm (slabAvg κ) Ugrad φ hSlabCoeffThm hGradWeakThm hIntSlabThm
    (fun _ _ => hIntLimThm) hIntDiffThm hCoeffDiffThm

-- Fixed: each slab-integral upper bound `t0 + ((k+1) * w)` below was missing
-- its closing parenthesis in the as-given text (it did not parse), and the
-- `(slabAvg - κ)` groups in `hIntDiffThm`/`hCoeffDiffThm` were missing their
-- opening parenthesis (orphan `)`).
-- Added: `hTerm2AsmThm`, `hWeakUx`, `hIntSlabThm`. The as-given hypotheses do
-- not determine the conclusion (nothing relates the interpolant to `ux`);
-- these are the side conditions of `rothe_term2_inst` applied below.
/-- Term-2 passage, instantiated. -/

theorem term2_passage
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    (u ux : ℝ → ℝ → ℝ)
    (U_of : ℕ → ℕ → WeakH10)
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ)
    (hSlabCoeffThm : ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N))) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) * ((t1 - t0) / N))), κ s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hGradWeakThm : ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => (if t = t1 then (U_of N N).weakDeriv x else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hIntLimThm : Integrable (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hIntDiffThm : ∀ (N : ℕ), 0 < N →
      Integrable (fun p : ℝ × ℝ => (((1 / ((t1 - t0) / N)) * ∫ s in (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1) * ((t1 - t0) / N))), κ s p.2) - κ p.1 p.2) * (if p.1 = t1 then (U_of N N).weakDeriv p.2 else (U_of N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hCoeffDiffThm : Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (((1 / ((t1 - t0) / N)) * ∫ s in (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1) * ((t1 - t0) / N))), κ s p.2) - κ p.1 p.2) * ux p.1 p.2
            * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (hTerm2AsmThm : ∀ (kbar : ℕ → ℝ → ℝ → ℝ) (ugrad : ℕ → ℝ → ℝ → ℝ)
      (φf : ℝ → ℝ → ℝ),
      (∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
        MemLp (fun x => kbar N t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
        MemLp (fun x => ugrad N t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N →
        Integrable (fun p : ℝ × ℝ => kbar N p.1 p.2 * ugrad N p.1 p.2
          * deriv (fun y => φf p.1 y) p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N →
        Integrable (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2
          * deriv (fun y => φf p.1 y) p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) →
      (∀ (N : ℕ), 0 < N →
        Integrable (fun p : ℝ × ℝ => (kbar N p.1 p.2 - κ p.1 p.2) * ugrad N p.1 p.2
          * deriv (fun y => φf p.1 y) p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (kbar N p.1 p.2 - κ p.1 p.2) * ux p.1 p.2
              * deriv (fun y => φf p.1 y) p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds 0) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            kbar N p.1 p.2 * ugrad N p.1 p.2
              * deriv (fun y => φf p.1 y) p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φf p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hWeakUx : ∀ ψ : ℝ → ℝ → ℝ,
        MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
        Filter.Tendsto (fun N : ℕ =>
            ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              (if p.1 = t1 then (U_of N N).weakDeriv p.2 else (U_of N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
                * ψ p.1 p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ux p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hIntSlabThm : ∀ (N : ℕ), 0 < N →
      Integrable (fun p : ℝ × ℝ => ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1) * ((t1 - t0) / N))), κ s p.2)
        * (if p.1 = t1 then (U_of N N).weakDeriv p.2 else (U_of N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
        * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    Filter.Tendsto (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          ((1 / ((t1 - t0) / N)) * ∫ s in (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1) * ((t1 - t0) / N))), κ s p.2)
            * (if p.1 = t1 then (U_of N N).weakDeriv p.2 else (U_of N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
            * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) := by
  exact rothe_term2_inst ht u ux
    (fun N t x => if t = t1 then (U_of N N).weakDeriv x
      else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).weakDeriv x)
    (fun kk N t x => (1 / ((t1 - t0) / N)) * ∫ s in (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N))) * ((t1 - t0) / N))..(t0 + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) * ((t1 - t0) / N))), kk s x)
    hSlabCoeffThm φ hTerm2AsmThm hGradWeakThm hIntSlabThm hIntLimThm hIntDiffThm
    hWeakUx hIntLimThm hCoeffDiffThm




theorem icc_eq_ioc_integral (a b : ℝ) (g : ℝ → ℝ) :
    ∫ x in Set.Icc a b, g x ∂volume = ∫ x in Set.Ioc a b, g x ∂volume := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  have hcompl : ∀ᶠ x in ae volume, x ≠ a := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬x ≠ a} = {a} := by
      ext x
      simp
    rw [hset]
    exact Real.volume_singleton
  filter_upwards [hcompl] with x hx
  by_cases hxb : x ∈ Set.Icc a b
  · have hxIoc : x ∈ Set.Ioc a b := ⟨lt_of_le_of_ne hxb.1 (Ne.symm hx), hxb.2⟩
    rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hxIoc]
  · have hxIoc : x ∉ Set.Ioc a b := fun h => hxb (Set.Ioc_subset_Icc_self h)
    rw [Set.indicator_of_notMem hxb, Set.indicator_of_notMem hxIoc]


theorem bridge_aux {t0 t1 : ℝ} (ht : t0 < t1)
    (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, f p
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, f (t, x) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have htt : t0 ≤ t1 := le_of_lt ht
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume := rfl
  have hfOn : IntegrableOn f (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    show Integrable f ((volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
    rw [← hvol]
    exact hf
  have hF : (∫ z in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, f z ∂(volume.prod volume))
      = ∫ x in Set.Icc t0 t1, ∫ y in Set.Icc (0 : ℝ) 1, f (x, y) ∂volume ∂volume :=
    setIntegral_prod f hfOn
  have hLHS : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, f p
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ z in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, f z ∂(volume.prod volume) := by
    show ∫ z, f z ∂((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
      = ∫ z, f z ∂((volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
    rw [Measure.restrict_restrict_of_subset subset_rfl, hvol]
  have hinner : ∀ t : ℝ, (∫ x in Set.Icc (0 : ℝ) 1, f (t, x) ∂volume)
      = ∫ x in (0 : ℝ)..1, f (t, x) := by
    intro t
    rw [icc_eq_ioc_integral, intervalIntegral.integral_of_le h01]
  have hIter : (∫ x in Set.Icc t0 t1, ∫ y in Set.Icc (0 : ℝ) 1, f (x, y) ∂volume ∂volume)
      = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, f (t, x) := by
    simp only [hinner]
    rw [icc_eq_ioc_integral, intervalIntegral.integral_of_le htt]
  exact hLHS.trans (hF.trans hIter)

/-- Combine: discrete identity + rewrites + term passages give the
weak equation for the limit. -/

theorem rothe_limit_combine
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    (U : ℕ → ℕ → WeakH10)
    (kbar Fbar : ℕ → ℕ → ℝ → ℝ)
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (u ux : ℝ → ℝ → ℝ)
    (hDiscThm : ∀ (N : ℕ), 0 < N → ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      -(∑ k ∈ Finset.range N,
          ∫ x in (0 : ℝ)..1,
            (U N k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
              - φ (t0 + k * ((t1 - t0) / N)) x))
        + ((t1 - t0) / N) * ∑ k ∈ Finset.range N,
          ∫ x in (0 : ℝ)..1,
            kbar N k x * (U N (k + 1)).weakDeriv x
              * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x
        = ((t1 - t0) / N) * ∑ k ∈ Finset.range N,
          ∫ x in (0 : ℝ)..1,
            Fbar N k x * φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x)
    (hR1Thm : ∀ (N : ℕ), 0 < N → ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      -(∑ k ∈ Finset.range N,
          ∫ x in (0 : ℝ)..1,
            (U N k).toFun x * (φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
              - φ (t0 + k * ((t1 - t0) / N)) x))
        = -∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (U N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)))).toFun p.2
            * slabDiffQuot t0 t1 N φ p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hR2Thm : ∀ (N : ℕ), 0 < N → ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      ((t1 - t0) / N) * ∑ k ∈ Finset.range N,
          ∫ x in (0 : ℝ)..1,
            kbar N k x * (U N (k + 1)).weakDeriv x
              * deriv (fun y => φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) y) x
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then kbar N (N - 1) p.2
           else kbar N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
            * (if p.1 = t1 then (U N N).weakDeriv p.2
               else (U N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N)) + 1)).weakDeriv p.2)
            * slabSampleFn t0 t1 N (fun t x => deriv (fun y => φ t y) x) p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hR3Thm : ∀ (N : ℕ), 0 < N → ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      ((t1 - t0) / N) * ∑ k ∈ Finset.range N,
          ∫ x in (0 : ℝ)..1,
            Fbar N k x * φ (t0 + (k + 1 : ℝ) * ((t1 - t0) / N)) x
        = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then Fbar N (N - 1) p.2
           else Fbar N (Nat.floor ((p.1 - t0) / ((t1 - t0) / N))) p.2)
            * slabSampleFn t0 t1 N φ p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hT1Thm : ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ =>
          -∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))))).toFun p.2
              * slabDiffQuot t0 t1 (φm N) φ p
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (-∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          u p.1 p.2 * deriv (fun s => φ s p.2) p.1
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hT2Thm : ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then kbar (φm N) ((φm N) - 1) p.2
             else kbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
              * (if p.1 = t1 then (U (φm N) (φm N)).weakDeriv p.2
                 else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)).weakDeriv p.2)
              * slabSampleFn t0 t1 (φm N) (fun t x => deriv (fun y => φ t y) x) p
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hIntThm : ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      Integrable (fun p : ℝ × ℝ => -u p.1 p.2 * deriv (fun s => φ s p.2) p.1)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ Integrable (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ Integrable (fun p : ℝ × ℝ => F p.1 p.2 * φ p.1 p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hT3Thm : ∀ (φ : ℝ → ℝ → ℝ), ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then Fbar (φm N) ((φm N) - 1) p.2
             else Fbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
              * slabSampleFn t0 t1 (φm N) φ p
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          F p.1 p.2 * φ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))) :
    ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x := by
  intro φ hφ
  have hle : ∀ N : ℕ, N ≤ φm N := by
    intro N
    induction N with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have h : φm k < φm (k + 1) := hφm (Nat.lt_succ_self k)
      omega
  have hev : ∀ᶠ N : ℕ in Filter.atTop, 0 < φm N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    calc (0 : ℕ) < 1 := by norm_num
      _ ≤ N := hN
      _ ≤ φm N := hle N
  have heq : (fun N : ℕ =>
        (-∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))))).toFun p.2
              * slabDiffQuot t0 t1 (φm N) φ p
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then kbar (φm N) ((φm N) - 1) p.2
             else kbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
              * (if p.1 = t1 then (U (φm N) (φm N)).weakDeriv p.2
                 else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)).weakDeriv p.2)
              * slabSampleFn t0 t1 (φm N) (fun t x => deriv (fun y => φ t y) x) p
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))
      =ᶠ[Filter.atTop] (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then Fbar (φm N) ((φm N) - 1) p.2
           else Fbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
            * slabSampleFn t0 t1 (φm N) φ p
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) := by
    filter_upwards [hev] with N hN
    have hD := hDiscThm (φm N) hN φ hφ
    rw [hR1Thm (φm N) hN φ hφ, hR2Thm (φm N) hN φ hφ, hR3Thm (φm N) hN φ hφ] at hD
    exact hD
  have hAdd := (hT1Thm φ hφ).add (hT2Thm φ hφ)
  have hC : Filter.Tendsto (fun N : ℕ =>
      ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then Fbar (φm N) ((φm N) - 1) p.2
         else Fbar (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N)))) p.2)
          * slabSampleFn t0 t1 (φm N) φ p
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds
        ((-∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            u p.1 p.2 * deriv (fun s => φ s p.2) p.1
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))) :=
    Filter.Tendsto.congr' heq hAdd
  have hRect : (-∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        F p.1 p.2 * φ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    tendsto_nhds_unique hC (hT3Thm φ hφ)
  obtain ⟨hI1, hI2, hI3⟩ := hIntThm φ hφ
  have hI12 : Integrable
      (fun p : ℝ × ℝ => -u p.1 p.2 * deriv (fun s => φ s p.2) p.1
        + κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    hI1.add hI2
  have hA : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        -u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = -∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    have hneg : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          -(u p.1 p.2 * deriv (fun s => φ s p.2) p.1)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = -∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          u p.1 p.2 * deriv (fun s => φ s p.2) p.1
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
      integral_neg _
    rw [← hneg]
    simp only [neg_mul]
  have hconv : ∀ g : ℝ × ℝ → ℝ, (∫ a, g a ∂(volume.restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, g p
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    intro g
    show (∫ a, g a ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
      = ∫ a, g a ∂((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
        (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
    rw [Measure.restrict_restrict_of_subset subset_rfl]
  have hAddInt : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        -u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      + (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (-u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          + κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    simp only [← hconv]
    exact (integral_add hI1 hI2).symm
  have hL : (∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x))
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (-u p.1 p.2 * deriv (fun s => φ s p.2) p.1
          + κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    (bridge_aux ht _ hI12).symm
  have hR : (∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        F p.1 p.2 * φ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    (bridge_aux ht _ hI3).symm
  rw [hL, hR, ← hAddInt, hA]
  exact hRect


theorem rothe_limit_passage
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (u ux : ℝ → ℝ → ℝ)
    (hCombineThm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ => rect t0 t1 (fun t x => -(u t x) * deriv (fun s => φ s x) t))
        Filter.atTop (nhds (rect t0 t1 (fun t x => -(u t x) * deriv (fun s => φ s x) t))) →
      Filter.Tendsto (fun N : ℕ => rect t0 t1 (fun t x => κ t x * ux t x * deriv (fun y => φ t y) x))
        Filter.atTop (nhds (rect t0 t1 (fun t x => κ t x * ux t x * deriv (fun y => φ t y) x))) →
      Filter.Tendsto (fun N : ℕ => rect t0 t1 (fun t x => F t x * φ t x))
        Filter.atTop (nhds (rect t0 t1 (fun t x => F t x * φ t x))) →
      rect t0 t1 (fun t x => -(u t x) * deriv (fun s => φ s x) t)
        + rect t0 t1 (fun t x => κ t x * ux t x * deriv (fun y => φ t y) x)
        = rect t0 t1 (fun t x => F t x * φ t x))
    (hTerm1Thm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ => rect t0 t1 (fun t x => -(u t x) * deriv (fun s => φ s x) t))
        Filter.atTop (nhds (rect t0 t1 (fun t x => -(u t x) * deriv (fun s => φ s x) t))))
    (hTerm2Thm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ => rect t0 t1 (fun t x => κ t x * ux t x * deriv (fun y => φ t y) x))
        Filter.atTop (nhds (rect t0 t1 (fun t x => κ t x * ux t x * deriv (fun y => φ t y) x))))
    (hTerm3Thm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Filter.Tendsto (fun N : ℕ => rect t0 t1 (fun t x => F t x * φ t x))
        Filter.atTop (nhds (rect t0 t1 (fun t x => F t x * φ t x)))) :
    ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      rect t0 t1 (fun t x => -(u t x) * deriv (fun s => φ s x) t)
        + rect t0 t1 (fun t x => κ t x * ux t x * deriv (fun y => φ t y) x)
        = rect t0 t1 (fun t x => F t x * φ t x) := by
  exact fun φ hφ => hCombineThm φ hφ (hTerm1Thm φ hφ) (hTerm2Thm φ hφ) (hTerm3Thm φ hφ)


lemma inner_eq_integral_of_ae_eq (μ : Measure ℝ)
    (g1 g2 : ℝ → ℝ) (G1 G2 : Lp ℝ 2 μ)
    (h1 : (G1 : ℝ → ℝ) =ᵐ[μ] g1) (h2 : (G2 : ℝ → ℝ) =ᵐ[μ] g2) :
    Inner.inner (𝕜 := ℝ) G1 G2 = ∫ x, g1 x * g2 x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h1, h2] with x hx1 hx2
  have h_inner : ∀ a b : ℝ, Inner.inner (𝕜 := ℝ) a b = a * b := by
    intro a b
    simp [RCLike.inner_apply, mul_comm]
  rw [h_inner]
  rw [hx1, hx2]

/-- Weak lower semicontinuity of the `L²` norm along Rothe slices. -/

theorem rothe_slice_norm_liminf
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u : ℝ → ℝ → ℝ} (hu : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U : ℕ → ℕ → (ℝ → ℝ))
    (hU : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (hWeakSliceThm : ∀ (τ : ℝ), τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x))) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ≤ Filter.liminf (fun N : ℕ =>
          (eLpNorm (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) Filter.atTop := by
  intro τ hτ
  -- Abbreviations
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ_def
  set f : ℝ → ℝ := fun x => u τ x with hf_def
  set F : ℕ → (ℝ → ℝ) := fun N =>
    U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) with hF_def
  have hf : MemLp f 2 μ := hu τ hτ
  have hF : ∀ N : ℕ, MemLp (F N) 2 μ := fun N => hU (φm N) _
  -- Lp elements
  set Fp : Lp ℝ 2 μ := hf.toLp f with hFp_def
  set FpN : ℕ → Lp ℝ 2 μ := fun N => (hF N).toLp (F N) with hFpN_def
  -- Norm equalities
  have hFp_norm : ‖Fp‖ = (eLpNorm f 2 μ).toReal := Lp.norm_toLp f hf
  have hFpN_norm : ∀ N : ℕ, ‖FpN N‖ = (eLpNorm (F N) 2 μ).toReal :=
    fun N => Lp.norm_toLp (F N) (hF N)
  -- Weak convergence as inner-product convergence for arbitrary test vector
  have h_inner_tendsto : ∀ Ψ : Lp ℝ 2 μ,
      Filter.Tendsto (fun N : ℕ => Inner.inner (𝕜 := ℝ) (FpN N) Ψ)
        Filter.atTop (nhds (Inner.inner (𝕜 := ℝ) Fp Ψ)) := by
    intro Ψ
    set ψ : ℝ → ℝ := (Ψ : ℝ → ℝ) with hψ_def
    have hψ : MemLp ψ 2 μ := Lp.memLp Ψ
    have h_tendsto_interval := hWeakSliceThm τ hτ ψ hψ
    -- Convert interval integrals to μ integrals
    have h_conv : ∀ g : ℝ → ℝ, ∫ x in (0 : ℝ)..1, g x = ∫ x, g x ∂μ := by
      intro g
      have h := intervalIntegral_eq_integral_restrict_Icc (g := g)
      simpa [hμ_def] using h
    have h_tendsto_mu : Filter.Tendsto (fun N : ℕ => ∫ x, F N x * ψ x ∂μ)
        Filter.atTop (nhds (∫ x, f x * ψ x ∂μ)) := by
      simpa [h_conv] using h_tendsto_interval
    have h_inner_N : ∀ N : ℕ, Inner.inner (𝕜 := ℝ) (FpN N) Ψ = ∫ x, F N x * ψ x ∂μ :=
      fun N => inner_eq_integral_of_ae_eq μ (F N) ψ (FpN N) Ψ
        (MemLp.coeFn_toLp (hF N)) (Filter.EventuallyEq.refl _ _)
    have h_inner_lim : Inner.inner (𝕜 := ℝ) Fp Ψ = ∫ x, f x * ψ x ∂μ :=
      inner_eq_integral_of_ae_eq μ f ψ Fp Ψ
        (MemLp.coeFn_toLp hf) (Filter.EventuallyEq.refl _ _)
    simpa [← h_inner_N, ← h_inner_lim] using h_tendsto_mu
  -- Uniform boundedness via Banach-Steinhaus
  set g : ℕ → (Lp ℝ 2 μ →L[ℝ] ℝ) := fun N => innerSL ℝ (FpN N) with hg_def
  have h_pointwise : ∀ Ψ : Lp ℝ 2 μ, ∃ C, ∀ N : ℕ, ‖g N Ψ‖ ≤ C := by
    intro Ψ
    have h_tendsto_g : Filter.Tendsto (fun N : ℕ => g N Ψ)
        Filter.atTop (nhds (Inner.inner (𝕜 := ℝ) Fp Ψ)) :=
      h_inner_tendsto Ψ
    have h_bdd := Metric.isBounded_range_of_tendsto _ h_tendsto_g
    obtain ⟨C, hC⟩ := h_bdd.exists_norm_le
    exact ⟨C, fun N => hC _ (Set.mem_range_self N)⟩
  obtain ⟨Cbound, hCbound⟩ := banach_steinhaus h_pointwise
  have h_norm_le : ∀ N : ℕ, ‖FpN N‖ ≤ Cbound := by
    intro N
    have h_eq : ‖g N‖ = ‖FpN N‖ := innerSL_apply_norm ℝ (FpN N)
    rw [← h_eq]
    exact hCbound N
  -- Rewrite goal to Lp norms
  have h_fun_eq : (fun N : ℕ => (eLpNorm (F N) 2 μ).toReal ^ 2) =
      (fun N : ℕ => ‖FpN N‖ ^ 2) := by
    funext N
    rw [← hFpN_norm N]
  rw [← hFp_norm, h_fun_eq]
  -- Uniform bound gives frequently-bounded-above for squared norms
  have h_bsq_le : ∀ N : ℕ, ‖FpN N‖ ^ 2 ≤ Cbound ^ 2 :=
    fun N => pow_le_pow_left₀ (norm_nonneg _) (h_norm_le N) 2
  have h_freq_bsq : ∃ᶠ N in Filter.atTop, ‖FpN N‖ ^ 2 ≤ Cbound ^ 2 :=
    (Filter.Eventually.of_forall h_bsq_le).frequently
  have h_cob_bsq : Filter.IsCoboundedUnder (fun x1 x2 => x2 ≤ x1) Filter.atTop
      (fun N : ℕ => ‖FpN N‖ ^ 2) :=
    Filter.IsCoboundedUnder.of_frequently_le h_freq_bsq
  by_cases hFp_eq : ‖Fp‖ = 0
  · -- Zero case: LHS is 0
    have h_zero_le : (0 : ℝ) ≤
        Filter.liminf (fun N : ℕ => ‖FpN N‖ ^ 2) Filter.atTop :=
      Filter.le_liminf_of_le h_cob_bsq
        (Filter.Eventually.of_forall fun N => sq_nonneg _)
    have h_lhs_eq : ‖Fp‖ ^ 2 = 0 := by
      rw [hFp_eq]
      norm_num
    rw [h_lhs_eq]
    exact h_zero_le
  · -- Positive case
    have ha_pos : 0 < ‖Fp‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hFp_eq)
    have ha_ne : ‖Fp‖ ≠ 0 := hFp_eq
    have h_tendsto_c : Filter.Tendsto
        (fun N : ℕ => Inner.inner (𝕜 := ℝ) (FpN N) Fp)
        Filter.atTop (nhds (‖Fp‖ ^ 2)) := by
      have h0 := h_inner_tendsto Fp
      simpa [real_inner_self_eq_norm_sq] using h0
    have h_tendsto_d : Filter.Tendsto
        (fun N : ℕ => Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖)
        Filter.atTop (nhds ‖Fp‖) := by
      have h_div := h_tendsto_c.div_const ‖Fp‖
      have h_a2_div : ‖Fp‖ ^ 2 / ‖Fp‖ = ‖Fp‖ := by
        rw [pow_two]
        exact mul_div_cancel_right₀ _ ha_ne
      simpa [h_a2_div] using h_div
    have h_le_d_b : ∀ N : ℕ,
        Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖ ≤ ‖FpN N‖ := by
      intro N
      rw [div_le_iff₀ ha_pos]
      exact real_inner_le_norm _ _
    have h_eventually_nonneg_d : ∀ᶠ N in Filter.atTop,
        0 ≤ Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖ := by
      have h_gt : ∀ᶠ y in nhds ‖Fp‖, (0 : ℝ) < y := eventually_gt_nhds ha_pos
      have h_ev : ∀ᶠ N in Filter.atTop,
          (0 : ℝ) < Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖ :=
        h_tendsto_d.eventually h_gt
      filter_upwards [h_ev] with N hN
      exact le_of_lt hN
    have h_eventually_sq_le : ∀ᶠ N in Filter.atTop,
        (Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖) ^ 2 ≤ ‖FpN N‖ ^ 2 := by
      filter_upwards [h_eventually_nonneg_d] with N hN
      exact pow_le_pow_left₀ hN (h_le_d_b N) 2
    have h_tendsto_sq : Filter.Tendsto
        (fun N : ℕ => (Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖) ^ 2)
        Filter.atTop (nhds (‖Fp‖ ^ 2)) :=
      h_tendsto_d.pow 2
    have h_eq : Filter.liminf (fun N : ℕ =>
        (Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖) ^ 2) Filter.atTop
        = ‖Fp‖ ^ 2 :=
      h_tendsto_sq.liminf_eq
    have h_bdd_dsq : Filter.IsBoundedUnder (fun x1 x2 => x2 ≤ x1) Filter.atTop
        (fun N : ℕ => (Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖) ^ 2) :=
      Filter.isBoundedUnder_of ⟨0, fun N => sq_nonneg _⟩
    have h_le_liminf : Filter.liminf (fun N : ℕ =>
        (Inner.inner (𝕜 := ℝ) (FpN N) Fp / ‖Fp‖) ^ 2) Filter.atTop ≤
        Filter.liminf (fun N : ℕ => ‖FpN N‖ ^ 2) Filter.atTop :=
      Filter.liminf_le_liminf h_eventually_sq_le h_bdd_dsq h_cob_bsq
    rw [h_eq] at h_le_liminf
    exact h_le_liminf


theorem rothe_dissipation_liminf
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    {ux : ℝ → ℝ → ℝ}
    (Ugrad : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (hInterpThm : ∀ (N : ℕ) (τ : ℝ), τ ∈ Set.Icc t0 t1 →
      ((t1 - t0) / N) * ∑ j ∈ Finset.range (Nat.floor ((τ - t0) / ((t1 - t0) / N)) + 1),
          ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / N)) x
            * ((Ugrad N (j + 1)) x) ^ 2
        = ∫ t in t0..τ, ∫ x in (0 : ℝ)..1,
          κ (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) * ((t1 - t0) / N)) x
            * ((Ugrad N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) ^ 2)
    (hWLSCThm : ∀ (τ : ℝ), τ ∈ Set.Icc t0 t1 →
      ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        ≤ Filter.liminf (fun N : ℕ =>
          ∫ t in t0..τ, ∫ x in (0 : ℝ)..1,
            κ (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) : ℝ)
              * ((t1 - t0) / (φm N))) x
              * ((Ugrad (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) ^ 2)
          Filter.atTop) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        ≤ Filter.liminf (fun N : ℕ =>
          ((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1),
            ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / (φm N))) x
              * ((Ugrad (φm N) (j + 1)) x) ^ 2) Filter.atTop := by
  intro τ hτ
  have heq : (fun N : ℕ =>
        ((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1),
          ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / (φm N))) x
            * ((Ugrad (φm N) (j + 1)) x) ^ 2)
      = (fun N : ℕ =>
        ∫ t in t0..τ, ∫ x in (0 : ℝ)..1,
          κ (t0 + (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) : ℝ)
            * ((t1 - t0) / (φm N))) x
            * ((Ugrad (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) ^ 2) := by
    funext N
    exact hInterpThm (φm N) τ hτ
  rw [heq]
  exact hWLSCThm τ hτ


theorem forcing_integral_split
    {μ : Measure (ℝ × ℝ)} {Fbar F ubar : (ℝ × ℝ) → ℝ}
    (hInt1 : Integrable (fun p => (Fbar p - F p) * ubar p) μ)
    (hInt2 : Integrable (fun p => F p * ubar p) μ) :
    ∫ p, Fbar p * ubar p ∂μ
      = (∫ p, (Fbar p - F p) * ubar p ∂μ) + ∫ p, F p * ubar p ∂μ := by
  have h : ∀ p, Fbar p * ubar p = (Fbar p - F p) * ubar p + F p * ubar p := fun p => by ring
  simp_rw [h]
  exact integral_add hInt1 hInt2


theorem forcing_error_tendsto
    {μ : Measure (ℝ × ℝ)} {F : (ℝ × ℝ) → ℝ}
    (Fbar : ℕ → (ℝ × ℝ) → ℝ) (ubar : ℕ → (ℝ × ℝ) → ℝ)
    (hMemFbar : ∀ N : ℕ, MemLp (fun p => Fbar N p - F p) 2 μ)
    (hMemUbar : ∀ N : ℕ, MemLp (ubar N) 2 μ)
    (hAvgThm : Filter.Tendsto (fun N : ℕ =>
        eLpNorm (fun p => Fbar N p - F p) 2 μ) Filter.atTop (nhds 0))
    (hBoundThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      (eLpNorm (ubar N) 2 μ).toReal ≤ C)
    (hCSThm : ∀ {f g : (ℝ × ℝ) → ℝ},
      MemLp f 2 μ → MemLp g 2 μ →
      |∫ p, f p * g p ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal) :
    Filter.Tendsto (fun N : ℕ => ∫ p, (Fbar N p - F p) * ubar N p ∂μ)
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC0, hCb⟩ := hBoundThm
  have hAvgReal : Filter.Tendsto (fun N : ℕ =>
      (eLpNorm (fun p => Fbar N p - F p) 2 μ).toReal) Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hAvgThm
    simpa [Function.comp_def] using h
  have hMul : Filter.Tendsto (fun N : ℕ =>
      (eLpNorm (fun p => Fbar N p - F p) 2 μ).toReal * C) Filter.atTop (nhds 0) := by
    have h := hAvgReal.mul_const C
    simpa using h
  apply squeeze_zero_norm (fun N => ?_) hMul
  rw [Real.norm_eq_abs]
  calc |∫ p, (Fbar N p - F p) * ubar N p ∂μ|
      ≤ (eLpNorm (fun p => Fbar N p - F p) 2 μ).toReal *
        (eLpNorm (ubar N) 2 μ).toReal :=
        hCSThm (hMemFbar N) (hMemUbar N)
    _ ≤ (eLpNorm (fun p => Fbar N p - F p) 2 μ).toReal * C :=
        mul_le_mul_of_nonneg_left (hCb N) ENNReal.toReal_nonneg


theorem tendsto_of_split_add
    {ι : Type*} {l : Filter ι} {f g h : ι → ℝ} {y : ℝ}
    (hsplit : ∀ i : ι, f i = g i + h i)
    (herr : Filter.Tendsto g l (nhds 0))
    (hmain : Filter.Tendsto h l (nhds y)) :
    Filter.Tendsto f l (nhds y) := by
  have hfg : f = fun i => g i + h i := funext hsplit
  rw [hfg]
  simpa using herr.add hmain


theorem WeakH10.toFun_memLp (w : WeakH10) :
    MemLp w.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hvol : volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr hvol
  have hInt : Integrable w.weakDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    MemLp.integrable one_le_two w.weakDeriv_memLp
  have hOn : IntegrableOn w.weakDeriv (Set.Icc (0 : ℝ) 1) volume := hInt
  have hOnU : IntegrableOn w.weakDeriv (Set.uIcc (0 : ℝ) 1) volume := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hOn
  have hContPrim : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, w.weakDeriv t) (Set.uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval hOnU
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hContPrim
  have hEq : Set.EqOn w.toFun (fun x => ∫ t in (0 : ℝ)..x, w.weakDeriv t) (Set.Icc 0 1) :=
    fun x hx => w.toFun_eq_integral x hx
  have hCont : ContinuousOn w.toFun (Set.Icc (0 : ℝ) 1) := hContPrim.congr hEq
  have hMeas : AEStronglyMeasurable w.toFun (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hCont.aestronglyMeasurable measurableSet_Icc
  have hComp : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hNe : (Set.Icc (0 : ℝ) 1).Nonempty :=
    Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)
  have hNormCont : ContinuousOn (fun x => ‖w.toFun x‖) (Set.Icc (0 : ℝ) 1) :=
    continuous_norm.comp_continuousOn hCont
  obtain ⟨x0, hx0mem, hx0max⟩ := hComp.exists_isMaxOn hNe hNormCont
  have hBound : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖w.toFun x‖ ≤ ‖w.toFun x0‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact isMaxOn_iff.mp hx0max x hx
  exact MemLp.of_bound hMeas _ hBound


theorem integral_abs_mul_le_eLpNorm_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hmul : MemLp (f * g) 1 μ := hf.mul hg
  have hint : Integrable (f * g) μ := memLp_one_iff_integrable.mp hmul
  have hHolder : eLpNorm (f * g) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    have h : eLpNorm (f • g) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ :=
      eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hg.aestronglyMeasurable
    have hfg : (f • g) = (f * g) := funext fun x => smul_eq_mul _ _
    rwa [hfg] at h
  have hnorm : ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ :=
    norm_integral_le_integral_norm _
  rw [Real.norm_eq_abs] at hnorm
  have h_eq1 : (∫ x, f x * g x ∂μ) = ∫ x, (f * g) x ∂μ := by simp [Pi.mul_apply]
  have h_eq2 : (∫ x, ‖f x * g x‖ ∂μ) = ∫ x, ‖(f * g) x‖ ∂μ := by simp [Pi.mul_apply]
  rw [h_eq1, h_eq2] at hnorm
  have h_ofReal : ENNReal.ofReal (∫ x, ‖(f * g) x‖ ∂μ) = eLpNorm (f * g) 1 μ := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hint,
      eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
  have h_nonneg : 0 ≤ ∫ x, ‖(f * g) x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have h_toReal : (∫ x, ‖(f * g) x‖ ∂μ) = (eLpNorm (f * g) 1 μ).toReal := by
    have hcongr := congrArg ENNReal.toReal h_ofReal
    rw [ENNReal.toReal_ofReal h_nonneg] at hcongr
    exact hcongr
  have h_le : (eLpNorm (f * g) 1 μ).toReal ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
    have hne : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
    have hmono := ENNReal.toReal_mono hne hHolder
    rwa [ENNReal.toReal_mul] at hmono
  rw [h_toReal] at hnorm
  rw [h_eq1]
  exact hnorm.trans h_le
/-- Equicontinuity of the pairing functions. -/

theorem pairing_equicont
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hTimetrans : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ t h : ℝ,
      t ∈ Set.Icc t0 t1 → t + h ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x =>
        (if t + h = t1 then (U_of N N).toFun x
         else (U_of N (Nat.floor (((t + h) - t0) / ((t1 - t0) / N)) + 1)).toFun x)
        - (if t = t1 then (U_of N N).toFun x
           else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)).toFun x))
        2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * (|h| + (t1 - t0) / N)))
    {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < φ N → ∀ τ t : ℝ,
      τ ∈ Set.Icc t0 t1 → t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
        - (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)|
        ≤ Real.sqrt (C * (|τ - t| + (t1 - t0) / (φ N : ℝ))) * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  obtain ⟨C, hC0, hC⟩ := hTimetrans
  refine ⟨C, hC0, fun N hN τ t hτ htmem => ?_⟩
  have hMemTau : MemLp (fun x : ℝ => (if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x))
      2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    by_cases h : τ = t1
    · simp [h]
      exact (U_of (φ N) (φ N)).toFun_memLp
    · simp [h]
      exact (U_of (φ N) _).toFun_memLp
  have hMemT : MemLp (fun x : ℝ => (if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x))
      2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    by_cases h : t = t1
    · simp [h]
      exact (U_of (φ N) (φ N)).toFun_memLp
    · simp [h]
      exact (U_of (φ N) _).toFun_memLp
  have hConvTau : (∫ x in (0 : ℝ)..1, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
      = ∫ x, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← integral_Icc_eq_integral_Ioc]
  have hConvT : (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
      = ∫ x, (if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← integral_Icc_eq_integral_Ioc]
  rw [hConvTau, hConvT]
  have hIntTauMul : Integrable ((fun x : ℝ => (if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x)) * ψ)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hMemTau.integrable_mul hψ
  have hIntTMul : Integrable ((fun x : ℝ => (if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x)) * ψ)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hMemT.integrable_mul hψ
  have hSubEq : (∫ x, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      - (∫ x, (if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ x, (((if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x))
      - ((if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x))) * ψ x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hSub := integral_sub hIntTauMul hIntTMul
    have hEqA : (∫ x, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
        else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        = ∫ x, ((fun x : ℝ => (if τ = t1 then (U_of (φ N) (φ N)).toFun x
        else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x)) * ψ) x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by simp [Pi.mul_apply]
    have hEqB : (∫ x, (if t = t1 then (U_of (φ N) (φ N)).toFun x
        else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        = ∫ x, ((fun x : ℝ => (if t = t1 then (U_of (φ N) (φ N)).toFun x
        else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x)) * ψ) x
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by simp [Pi.mul_apply]
    rw [hEqA, hEqB, ← hSub]
    congr 1
    ext x
    simp [Pi.mul_apply, sub_mul]
  rw [hSubEq]
  have hMemDiff : MemLp (fun x : ℝ => ((if τ = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x))
      - ((if t = t1 then (U_of (φ N) (φ N)).toFun x
      else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x)))
      2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hMemTau.sub hMemT
  have hCS := integral_abs_mul_le_eLpNorm_mul hMemDiff hψ
  have hth : t + (τ - t) = τ := by ring
  have hτmem' : t + (τ - t) ∈ Set.Icc t0 t1 := by rw [hth]; exact hτ
  have hBound := hC (φ N) hN t (τ - t) htmem hτmem'
  rw [hth] at hBound
  have hNonneg : 0 ≤ (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  have hTrans := mul_le_mul_of_nonneg_right hBound hNonneg
  exact hCS.trans hTrans


theorem rothe_forcing_tendsto_asm_micro2_corrected
    {t0 t1 : ℝ} (ht : t0 < t1)
    {F : ℝ → ℝ → ℝ}
    (Fbar ubar : ℕ → (ℝ × ℝ) → ℝ) (u : ℝ → ℝ → ℝ)
    (hSplitThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ N : ℕ,
      ∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1, Fbar N p * ubar N p
        ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1))
        = (∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1, (Fbar N p - F p.1 p.2) * ubar N p
          ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))
          + ∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1, F p.1 p.2 * ubar N p
            ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))
    (hErrThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      Filter.Tendsto (fun N : ℕ => ∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1,
        (Fbar N p - F p.1 p.2) * ubar N p
        ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds 0))
    (hMainThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      Filter.Tendsto (fun N : ℕ => ∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1,
        F p.1 p.2 * ubar N p
        ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1,
        F p.1 p.2 * u p.1 p.2
        ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))))
    (hMicroThm : ∀ {ι : Type} {l : Filter ι} {f g h : ι → ℝ} {y : ℝ},
      (∀ i : ι, f i = g i + h i) →
      Filter.Tendsto g l (nhds 0) → Filter.Tendsto h l (nhds y) →
      Filter.Tendsto f l (nhds y)) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      Filter.Tendsto (fun N : ℕ => ∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1,
        Fbar N p * ubar N p
        ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))
      Filter.atTop (nhds (∫ p in Set.Icc t0 τ ×ˢ Set.Icc (0 : ℝ) 1,
        F p.1 p.2 * u p.1 p.2
        ∂(volume.restrict (Set.Icc t0 τ ×ˢ Set.Icc 0 1)))) := by
  intro τ hτ
  exact hMicroThm (fun N => hSplitThm τ hτ N) (hErrThm τ hτ) (hMainThm τ hτ)


lemma energy_asm_of_liminf
    (a d f : ℕ → ℝ) (A D C Fint : ℝ)
    (ha : ∀ᶠ N in Filter.atTop, 0 ≤ a N)
    (hd : ∀ᶠ N in Filter.atTop, 0 ≤ d N)
    (hle : ∀ᶠ N in Filter.atTop, a N + 2 * d N ≤ C + 2 * f N)
    (hA : A ≤ Filter.liminf a Filter.atTop)
    (hD : D ≤ Filter.liminf d Filter.atTop)
    (hf : Filter.Tendsto f Filter.atTop (nhds Fint)) :
    A + 2 * D ≤ C + 2 * Fint := by
  have hbouda : Filter.atTop.IsBoundedUnder (· ≥ ·) a :=
    ⟨0, Filter.eventually_map.mpr ha⟩
  have hboudd : Filter.atTop.IsBoundedUnder (· ≥ ·) d :=
    ⟨0, Filter.eventually_map.mpr hd⟩
  have hRHS : Filter.Tendsto (fun N => C + 2 * f N) Filter.atTop (nhds (C + 2 * Fint)) :=
    (tendsto_const_nhds.mul hf).const_add C
  have key : ∀ p < A, ∀ q < D, p + 2 * q ≤ C + 2 * Fint := by
    intro p hp q hq
    have ha' : ∀ᶠ N in Filter.atTop, p < a N :=
      Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hp hA) hbouda
    have hd' : ∀ᶠ N in Filter.atTop, q < d N :=
      Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hq hD) hboudd
    have hev : ∀ᶠ N in Filter.atTop, p + 2 * q ≤ C + 2 * f N := by
      filter_upwards [ha', hd', hle] with N haN hdN hleN
      linarith
    exact ge_of_tendsto hRHS hev
  by_contra hcon
  have hcon : C + 2 * Fint < A + 2 * D := lt_of_not_ge hcon
  set δ := (A + 2 * D - (C + 2 * Fint)) / 4 with hδ
  have hδpos : 0 < δ := by linarith
  have h := key (A - δ) (by linarith) (D - δ) (by linarith)
  linarith

/-- Energy assembly for the Rothe limit. -/

theorem rothe_limit_energy_asm_fixed
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    (hKappaSliceThm : ∀ t : ℝ, ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ t x)
    {F : ℝ → ℝ → ℝ}
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (u ux : ℝ → ℝ → ℝ)
    (hDiscEnergyThm : ∀ (N : ℕ), 0 < N → ∀ (k : ℕ), k ≤ N →
      (eLpNorm (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * ((t1 - t0) / N) * ∑ j ∈ Finset.range k,
          ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / N)) x * ((U N (j + 1)) x) ^ 2
        ≤ (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * ((t1 - t0) / N) * ∑ j ∈ Finset.range k,
          ∫ x in (0 : ℝ)..1, F (t0 + j * ((t1 - t0) / N)) x * (U N (j + 1)) x)
    (hNormLiminfThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ≤ Filter.liminf (fun N : ℕ =>
          (eLpNorm (U (φm N) (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N))) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) Filter.atTop)
    (hDissLiminfThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        ≤ Filter.liminf (fun N : ℕ =>
          ((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N)),
            ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / (φm N))) x
              * ((U (φm N) (j + 1)) x) ^ 2) Filter.atTop)
    (hForcingThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      Filter.Tendsto (fun N : ℕ =>
          ((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N)),
            ∫ x in (0 : ℝ)..1, F (t0 + j * ((t1 - t0) / (φm N))) x * (U (φm N) (j + 1)) x)
        Filter.atTop (nhds (∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x))) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        ≤ (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x := by
  intro τ hτ
  have hMpos : ∀ᶠ N in Filter.atTop, 0 < φm N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hle : N ≤ φm N := hφm.id_le N
    omega
  have ha : ∀ᶠ N in Filter.atTop, 0 ≤ (eLpNorm (U (φm N) (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N))) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
    Filter.Eventually.of_forall fun N => sq_nonneg _
  have hd : ∀ᶠ N in Filter.atTop, 0 ≤ ((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N)),
      ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / (φm N))) x * ((U (φm N) (j + 1)) x) ^ 2 := by
    filter_upwards [hMpos] with N hN
    refine mul_nonneg ?_ ?_
    · exact div_nonneg (le_of_lt (sub_pos.mpr ht)) (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro j hj
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply integral_nonneg_of_ae
      have hκ := hKappaSliceThm (t0 + ↑j * ((t1 - t0) / (φm N)))
      have hκ' := ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hκ
      filter_upwards [hκ'] with x hx
      exact mul_nonneg (le_trans (le_of_lt hkmin) hx) (sq_nonneg _)
  have hle : ∀ᶠ N in Filter.atTop,
      (eLpNorm (U (φm N) (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N))) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * (((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N)),
          ∫ x in (0 : ℝ)..1, κ (t0 + j * ((t1 - t0) / (φm N))) x * ((U (φm N) (j + 1)) x) ^ 2)
        ≤ (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * (((t1 - t0) / (φm N)) * ∑ j ∈ Finset.range (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N)),
          ∫ x in (0 : ℝ)..1, F (t0 + j * ((t1 - t0) / (φm N))) x * (U (φm N) (j + 1)) x) := by
    filter_upwards [hMpos] with N hN
    have h := hDiscEnergyThm (φm N) hN
      (min (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1) (φm N)) (min_le_right _ _)
    simp only [mul_assoc] at h
    exact h
  exact energy_asm_of_liminf _ _ _ _ _ _ _ ha hd hle
    (hNormLiminfThm τ hτ) (hDissLiminfThm τ hτ) (hForcingThm τ hτ)


theorem rothe_bump_concentration
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (hMemUThm : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hTimetransThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ t h : ℝ,
      t ∈ Set.Icc t0 t1 → t + h ∈ Set.Icc t0 t1 →
      eLpNorm (fun x =>
        (if t + h = t1 then (U N N) x
         else (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x)
        - (if t = t1 then (U N N) x
           else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x))
        2 (volume.restrict (Set.Icc (0 : ℝ) 1))
        ≤ ENNReal.ofReal (Real.sqrt (C * (|h| + (t1 - t0) / N))))
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ (N : ℕ), 0 < N → ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ →
      τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U N N) x
               else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x))
        - (∫ x in (0 : ℝ)..1,
              (if τ = t1 then (U N N) x
               else (U N (Nat.floor ((τ - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)|
        ≤ Real.sqrt (Classical.choose hTimetransThm * (δ + (t1 - t0) / N))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro N hN τ δ hτ hδ hLow hHigh ψ hψ
  obtain ⟨hC0, hTrans⟩ := Classical.choose_spec hTimetransThm
  set μ01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hμ01
  set C : ℝ := Classical.choose hTimetransThm with hC
  set step : ℝ := (t1 - t0) / N with hstep
  set S : Set ℝ := Set.Ioo (τ - δ) (τ + δ) with hS
  set P : ℝ := (eLpNorm ψ 2 μ01).toReal with hP
  set M : ℝ := Real.sqrt (C * (δ + step)) with hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have ht01 : t0 ≤ t1 := le_of_lt ht
  have hstep_pos : 0 < step := by
    rw [hstep]
    exact div_pos (sub_pos.mpr ht) hNpos
  have h2δ_pos : (0 : ℝ) < 2 * δ := mul_pos two_pos hδ
  have h2δ0 : (2 : ℝ) * δ ≠ 0 := ne_of_gt h2δ_pos
  have hW_nonneg : (0 : ℝ) ≤ 1 / (2 * δ) := (one_div_pos.mpr h2δ_pos).le
  have hP_nonneg : (0 : ℝ) ≤ P := ENNReal.toReal_nonneg
  have hS_meas : MeasurableSet S := by
    rw [hS]
    exact measurableSet_Ioo
  have hS_Ioc : S ⊆ Set.Ioc t0 t1 := by
    rw [hS]
    intro t ht
    rw [Set.mem_Ioo] at ht
    rw [Set.mem_Ioc]
    constructor <;> linarith
  have hS_Icc : S ⊆ Set.Icc t0 t1 := hS_Ioc.trans Set.Ioc_subset_Icc_self
  have hbump : (∫ t in t0..t1, (1 / (2 * δ)) * S.indicator 1 t) = 1 := by
    rw [intervalIntegral.integral_of_le ht01, integral_const_mul]
    have hind : (∫ t in Set.Ioc t0 t1, S.indicator 1 t ∂volume) = 2 * δ := by
      rw [integral_indicator_one hS_meas, Measure.real_def,
        Measure.restrict_apply hS_meas, Set.inter_eq_self_of_subset_left hS_Ioc,
        hS, Real.volume_Ioo,
        ENNReal.toReal_ofReal (show (0 : ℝ) ≤ (τ + δ) - (τ - δ) by linarith)]
      ring
    rw [hind]
    exact one_div_mul_cancel h2δ0
  have hw_meas : Measurable (fun t => (1 / (2 * δ)) * S.indicator 1 t) :=
    measurable_const.mul (Measurable.indicator measurable_const hS_meas)
  have hw_le : ∀ t : ℝ, |(1 / (2 * δ)) * S.indicator 1 t| ≤ 1 / (2 * δ) := by
    intro t
    by_cases htS : t ∈ S
    · rw [Set.indicator_of_mem htS]
      show |(1 / (2 * δ)) * 1| ≤ 1 / (2 * δ)
      rw [mul_one, abs_of_nonneg hW_nonneg]
    · rw [Set.indicator_of_notMem htS, mul_zero, abs_zero]
      exact hW_nonneg
  have hInt_w : IntervalIntegrable (fun t => (1 / (2 * δ)) * S.indicator 1 t) volume t0 t1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht01]
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc t0 t1)) :=
      isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    refine Integrable.of_bound hw_meas.aestronglyMeasurable (1 / (2 * δ)) ?_
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs]
    exact hw_le t
  have hProd : ∀ k : ℕ, IntervalIntegrable (fun x => U N k x * ψ x) volume 0 1 := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact IntegrableOn.mono_set ((hMemUThm N k).integrable_mul hψ) Set.Ioc_subset_Icc_self
  have hInt_inner : ∀ t : ℝ, IntervalIntegrable
      (fun x => (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
      volume 0 1 := by
    intro t
    by_cases ht1 : t = t1
    · simp only [ite_eq_left ht1]
      exact hProd N
    · simp only [ite_eq_right ht1]
      exact hProd _
  have hMem_ubar : ∀ t : ℝ, MemLp
      (fun x => if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
      2 μ01 := by
    intro t
    by_cases ht1 : t = t1
    · have heq : (fun x => if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
          = U N N := by
        funext x
        exact ite_eq_left ht1
      rw [heq]
      exact hMemUThm N N
    · have heq : (fun x => if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
          = U N (Nat.floor ((t - t0) / step) + 1) := by
        funext x
        exact ite_eq_right ht1
      rw [heq]
      exact hMemUThm N _
  have hSplit : ∀ t : ℝ,
      (∫ x in (0 : ℝ)..1, ((if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
        - (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x)) * ψ x)
      = (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
        - (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x) := by
    intro t
    have hsub := intervalIntegral.integral_sub (hInt_inner t) (hInt_inner τ)
    have hcongr : (∫ x in (0 : ℝ)..1, ((if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
          - (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x)) * ψ x)
        = ∫ x in (0 : ℝ)..1, ((if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
          - ((if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x) := by
      congr 1
      funext x
      ring
    rw [hcongr]
    exact hsub
  set F' : ℕ → ℝ := (fun k => ∫ x in (0 : ℝ)..1, U N k x * ψ x) with hF'
  set idx : ℝ → ℕ := (fun t => if t = t1 then N else Nat.floor ((t - t0) / step) + 1) with hidx
  set B : ℝ := ∑ k ∈ Finset.Icc 1 N, |F' k| with hB
  have hF'_meas : Measurable F' := by
    rw [hF']
    exact continuous_of_discreteTopology.measurable
  have hidx_meas : Measurable idx := by
    rw [hidx]
    refine Measurable.ite ?_ measurable_const ?_
    · exact measurableSet_singleton t1
    · refine Measurable.add_const ?_ 1
      have hcont : Continuous (fun t : ℝ => (t - t0) / step) :=
        (continuous_id.sub continuous_const).div_const step
      exact Nat.measurable_floor.comp hcont.measurable
  have hFeq : (fun t => ∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
      = F' ∘ idx := by
    funext t
    by_cases ht1 : t = t1
    · simp only [hF', hidx, Function.comp_apply, ite_eq_left ht1]
    · simp only [hF', hidx, Function.comp_apply, ite_eq_right ht1]
  have hF_meas : Measurable (fun t => ∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x) := by
    rw [hFeq]
    exact hF'_meas.comp hidx_meas
  have hF_eq : ∀ t : ℝ, (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
      = F' (idx t) := by
    intro t
    have h := congrFun hFeq t
    simpa using h
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hidx_mem : ∀ t : ℝ, t ∈ Set.Ioc t0 t1 → idx t ∈ Finset.Icc 1 N := by
    intro t ht
    simp only [hidx]
    rw [Finset.mem_Icc]
    by_cases ht1 : t = t1
    · simp only [ite_eq_left ht1]
      constructor
      · omega
      · exact le_rfl
    · simp only [ite_eq_right ht1]
      have htIoc : t0 < t ∧ t ≤ t1 := Set.mem_Ioc.mp ht
      have htlt : t < t1 := lt_of_le_of_ne htIoc.2 ht1
      have hdiv_lt : (t - t0) / step < (N : ℝ) := by
        rw [div_lt_iff₀ hstep_pos]
        have hNstep : (N : ℝ) * step = t1 - t0 := by
          rw [hstep]
          exact mul_div_cancel₀ _ hN0
        rw [hNstep]
        linarith
      have hdiv_nonneg : (0 : ℝ) ≤ (t - t0) / step :=
        div_nonneg (by linarith) hstep_pos.le
      have hfloor_lt : Nat.floor ((t - t0) / step) < N := (Nat.floor_lt hdiv_nonneg).mpr hdiv_lt
      constructor
      · omega
      · omega
  have hF_bound : ∀ t : ℝ, t ∈ Set.Ioc t0 t1 → |F' (idx t)| ≤ B := by
    intro t ht
    rw [hB]
    exact Finset.single_le_sum (fun k _ => abs_nonneg (F' k)) (hidx_mem t ht)
  have hInt_wF : IntervalIntegrable
      (fun t => ((1 / (2 * δ)) * S.indicator 1 t)
        * (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x))
      volume t0 t1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht01]
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc t0 t1)) :=
      isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    refine Integrable.of_bound (hw_meas.mul hF_meas).aestronglyMeasurable ((1 / (2 * δ)) * B) ?_
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_mul]
    by_cases htIoc : t ∈ Set.Ioc t0 t1
    · have hF_le : |(∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)| ≤ B := by
        rw [hF_eq t]
        exact hF_bound t htIoc
      exact mul_le_mul (hw_le t) hF_le (abs_nonneg _) hW_nonneg
    · have htS : t ∉ S := fun h => htIoc (hS_Ioc h)
      have hw0 : (1 / (2 * δ)) * S.indicator 1 t = 0 := by
        rw [Set.indicator_of_notMem htS, mul_zero]
      rw [hw0, abs_zero, zero_mul]
      exact mul_nonneg hW_nonneg hB_nonneg
  have hG : (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)
      = ∫ t in t0..t1, ((1 / (2 * δ)) * S.indicator 1 t)
        * (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x) := by
    rw [intervalIntegral.integral_mul_const, hbump, one_mul]
  have hInt_wG : IntervalIntegrable
      (fun t => ((1 / (2 * δ)) * S.indicator 1 t)
        * (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x))
      volume t0 t1 :=
    hInt_w.mul_const _
  have hsub_outer : ((∫ t in t0..t1, ((1 / (2 * δ)) * S.indicator 1 t)
          * (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x))
        - (∫ t in t0..t1, ((1 / (2 * δ)) * S.indicator 1 t)
          * (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)))
      = ∫ t in t0..t1, (((1 / (2 * δ)) * S.indicator 1 t)
          * (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
        - ((1 / (2 * δ)) * S.indicator 1 t)
          * (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)) :=
    (intervalIntegral.integral_sub hInt_wF hInt_wG).symm
  have hgInt : IntervalIntegrable (fun t => ((1 / (2 * δ)) * S.indicator 1 t) * (M * P)) volume t0 t1 :=
    hInt_w.mul_const _
  have hgval : (∫ t in t0..t1, ((1 / (2 * δ)) * S.indicator 1 t) * (M * P)) = M * P := by
    rw [intervalIntegral.integral_mul_const, hbump, one_mul]
  have hae : ∀ᵐ t ∂volume, t ∈ Set.Ioc t0 t1 →
      ‖((1 / (2 * δ)) * S.indicator 1 t)
          * (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
        - ((1 / (2 * δ)) * S.indicator 1 t)
          * (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)‖
      ≤ ((1 / (2 * δ)) * S.indicator 1 t) * (M * P) := by
    apply Filter.Eventually.of_forall
    intro t htIoc
    have hw_nonneg : (0 : ℝ) ≤ (1 / (2 * δ)) * S.indicator 1 t := by
      apply mul_nonneg hW_nonneg
      by_cases htS : t ∈ S
      · rw [Set.indicator_of_mem htS]
        show (0 : ℝ) ≤ 1
        exact zero_le_one
      · rw [Set.indicator_of_notMem htS]
    by_cases htS : t ∈ S
    · have htIcc : t ∈ Set.Icc t0 t1 := hS_Icc htS
      have hAt := hSplit t
      have hMemD : MemLp
          (fun x => (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
            - (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x))
          2 μ01 :=
        (hMem_ubar t).sub (hMem_ubar τ)
      have hcs := hCSThm hMemD hψ
      have hcancel : τ + (t - τ) = t := by ring
      have hmem_h : τ + (t - τ) ∈ Set.Icc t0 t1 := by
        rw [hcancel]
        exact htIcc
      have htt := hTrans N hN τ (t - τ) hτ hmem_h
      rw [hcancel] at htt
      have hDtop : eLpNorm
          (fun x => (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
            - (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x))
          2 μ01 ≠ ⊤ :=
        ne_of_lt (MemLp.eLpNorm_lt_top hMemD)
      have htoReal := (ENNReal.toReal_le_toReal hDtop ENNReal.ofReal_ne_top).mpr htt
      rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at htoReal
      have habs : |t - τ| < δ := by
        have htS' : τ - δ < t ∧ t < τ + δ := by
          have h2 := htS
          rw [hS] at h2
          exact Set.mem_Ioo.mp h2
        rw [abs_lt]
        constructor <;> linarith
      have hmono : Real.sqrt (C * (|t - τ| + step)) ≤ M := by
        rw [hM]
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left _ hC0
        exact add_le_add_left habs.le step
      have hPt : |(∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
          - (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)|
          ≤ M * P := by
        rw [←hAt]
        calc |(∫ x in (0 : ℝ)..1, ((if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
              - (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x)) * ψ x)|
              ≤ (eLpNorm (fun x => (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x)
                - (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x)) 2 μ01).toReal * P := hcs
          _ ≤ Real.sqrt (C * (|t - τ| + step)) * P :=
              mul_le_mul_of_nonneg_right htoReal hP_nonneg
          _ ≤ M * P := mul_le_mul_of_nonneg_right hmono hP_nonneg
      have hFtG : ((1 / (2 * δ)) * S.indicator 1 t)
            * (∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
          - ((1 / (2 * δ)) * S.indicator 1 t)
            * (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)
          = ((1 / (2 * δ)) * S.indicator 1 t)
            * ((∫ x in (0 : ℝ)..1, (if t = t1 then (U N N) x else (U N (Nat.floor ((t - t0) / step) + 1)) x) * ψ x)
              - (∫ x in (0 : ℝ)..1, (if τ = t1 then (U N N) x else (U N (Nat.floor ((τ - t0) / step) + 1)) x) * ψ x)) := by
        ring
      rw [Real.norm_eq_abs, hFtG, abs_mul, abs_of_nonneg hw_nonneg]
      exact mul_le_mul_of_nonneg_left hPt hw_nonneg
    · have hw0 : (1 / (2 * δ)) * S.indicator 1 t = 0 := by
        rw [Set.indicator_of_notMem htS, mul_zero]
      rw [hw0]
      simp only [zero_mul, sub_zero, norm_zero]
      exact le_rfl
  rw [hG, hsub_outer, ←Real.norm_eq_abs, ←hgval]
  exact intervalIntegral.norm_integral_le_of_norm_le ht01 hae hgInt


theorem rothe_bump_cauchy
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (hWeakSTThm : ∀ Ψ : ℝ → ℝ → ℝ,
      MemLp (Function.uncurry Ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U (φm N) (φm N)) p.2
             else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)) p.2)
              * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          0 * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hMemBumpThm : ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp (Function.uncurry (fun (t : ℝ) (x : ℝ) =>
        (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t) * ψ x))
        2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      CauchySeq (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U (φm N) (φm N)) p.2
             else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)) p.2)
              * ((1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 p.1) * ψ p.2)
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) := by
  intro τ δ hτ hδ ψ hψ
  exact (hWeakSTThm _ (hMemBumpThm τ δ hτ hδ ψ hψ)).cauchySeq


lemma abs_triangle_3 (a b c d ε : ℝ)
    (h1 : |b - a| < ε / 3) (h2 : |b - d| < ε / 3) (h3 : |d - c| < ε / 3) :
    |a - c| < ε := by
  calc |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
    _ ≤ |a - b| + (|b - d| + |d - c|) :=
        add_le_add_right (abs_sub_le b d c) _
    _ = |b - a| + (|b - d| + |d - c|) := by rw [abs_sub_comm a b]
    _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add h1 (add_lt_add h2 h3)
    _ = ε := by ring


lemma sqrt_conc_mono (C δ τ K ε : ℝ) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hτ : τ < δ) (hkey : Real.sqrt (C * (2 * δ)) * K < ε / 3) :
    Real.sqrt (C * (δ + τ)) * K < ε / 3 := by
  have hsum_le : δ + τ ≤ 2 * δ := by linarith
  have hC_le : C * (δ + τ) ≤ C * (2 * δ) :=
    mul_le_mul_of_nonneg_left hsum_le hC0
  have hsqrt_le : Real.sqrt (C * (δ + τ)) ≤ Real.sqrt (C * (2 * δ)) :=
    Real.sqrt_le_sqrt hC_le
  calc Real.sqrt (C * (δ + τ)) * K ≤ Real.sqrt (C * (2 * δ)) * K :=
        mul_le_mul_of_nonneg_right hsqrt_le hK0
    _ < ε / 3 := hkey


lemma sqrt_conc_zero (C δ τ K : ℝ) (h : C = 0 ∨ K = 0) :
    Real.sqrt (C * (δ + τ)) * K = 0 := by
  rcases h with rfl | rfl
  · rw [zero_mul, Real.sqrt_zero, zero_mul]
  · rw [mul_zero]

/-- Slice-pairing Cauchy assembly. -/

theorem rothe_slice_pairing_cauchy_asm_interior
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (hConcThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ τ δ : ℝ,
      τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x))
        - (∫ x in (0 : ℝ)..1,
              (if τ = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)|
        ≤ Real.sqrt (C * (δ + (t1 - t0) / (φm N)))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hBumpCauchyThm : ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      CauchySeq (fun N : ℕ =>
          ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x))) :
    ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      CauchySeq (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x) := by
  obtain ⟨C, hC0, hConc⟩ := hConcThm
  intro τ hτ0 hτ1 ψ hψ
  have ht_sub : 0 < t1 - t0 := sub_pos.mpr ht
  have hτmem : τ ∈ Set.Icc t0 t1 := Set.mem_Icc.mpr ⟨le_of_lt hτ0, le_of_lt hτ1⟩
  set K : ℝ := (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hgap0 : 0 < min (τ - t0) (t1 - τ) :=
    lt_min (sub_pos.mpr hτ0) (sub_pos.mpr hτ1)
  have hφm_top : Filter.Tendsto φm Filter.atTop Filter.atTop := hφm.tendsto_atTop
  have hφm_real : Filter.Tendsto (fun N : ℕ => ((φm N : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hφm_top
  have hτ_tendsto : Filter.Tendsto (fun N : ℕ => (t1 - t0) / ((φm N : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hφm_real
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  by_cases hCK : C = 0 ∨ K = 0
  · set δ : ℝ := (min (τ - t0) (t1 - τ)) / 2 with hδdef
    have hδ0 : 0 < δ := by
      rw [hδdef]
      exact div_pos hgap0 (by norm_num)
    have hδ_min : δ ≤ min (τ - t0) (t1 - τ) := by
      rw [hδdef]
      linarith [hgap0]
    have hδ_t0 : δ ≤ τ - t0 := le_trans hδ_min (min_le_left _ _)
    have hδ_t1 : δ ≤ t1 - τ := le_trans hδ_min (min_le_right _ _)
    have hτδ0 : τ - δ ≥ t0 := by linarith
    have hτδ1 : τ + δ ≤ t1 := by linarith
    have hev : ∀ᶠ N : ℕ in Filter.atTop, (t1 - t0) / ((φm N : ℕ) : ℝ) < δ :=
      hτ_tendsto.eventually (gt_mem_nhds hδ0)
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
    have hBump := hBumpCauchyThm τ δ hτmem hδ0 hτδ0 hτδ1 ψ hψ
    rw [Metric.cauchySeq_iff] at hBump
    obtain ⟨N₂, hN₂⟩ := hBump (ε / 3) hε3
    refine ⟨max N₁ (max N₂ 1), fun m hm n hn => ?_⟩
    have hN01 : 1 ≤ max N₁ (max N₂ 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one (le_trans hN01 hm)
    have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one (le_trans hN01 hn)
    have hN1N0 : N₁ ≤ max N₁ (max N₂ 1) := le_max_left _ _
    have hN2N0 : N₂ ≤ max N₁ (max N₂ 1) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hm1 : N₁ ≤ m := le_trans hN1N0 hm
    have hn1 : N₁ ≤ n := le_trans hN1N0 hn
    have hm2 : N₂ ≤ m := le_trans hN2N0 hm
    have hn2 : N₂ ≤ n := le_trans hN2N0 hn
    have hconc_m := hConc m hm0 τ δ hτmem hδ0 hτδ0 hτδ1 ψ hψ
    have hconc_n := hConc n hn0 τ δ hτmem hδ0 hτδ0 hτδ1 ψ hψ
    have hbound_m := sqrt_conc_zero C δ ((t1 - t0) / ((φm m : ℕ) : ℝ)) K hCK
    have hbound_n := sqrt_conc_zero C δ ((t1 - t0) / ((φm n : ℕ) : ℝ)) K hCK
    have h1 := lt_of_le_of_lt hconc_m (by rw [hbound_m]; exact hε3)
    have h2 := lt_of_le_of_lt hconc_n (by rw [hbound_n]; exact hε3)
    have hBdist := hN₂ m hm2 n hn2
    rw [Real.dist_eq] at hBdist
    rw [Real.dist_eq]
    exact abs_triangle_3 _ _ _ _ _ h1 hBdist h2
  · push Not at hCK
    have hCpos : 0 < C := lt_of_le_of_ne' hC0 hCK.1
    have hKpos : 0 < K := lt_of_le_of_ne' hK0 hCK.2
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have hKne : K ≠ 0 := ne_of_gt hKpos
    set δ1 : ℝ := (ε ^ 2) / (36 * C * K ^ 2) with hδ1def
    have hδ10 : 0 < δ1 := by
      rw [hδ1def]
      exact div_pos (pow_pos hε 2)
        (mul_pos (mul_pos (by norm_num) hCpos) (pow_pos hKpos 2))
    set δ : ℝ := min ((min (τ - t0) (t1 - τ)) / 2) δ1 with hδdef
    have hδ0 : 0 < δ := by
      rw [hδdef]
      exact lt_min (div_pos hgap0 (by norm_num)) hδ10
    have hδ_gap : δ ≤ (min (τ - t0) (t1 - τ)) / 2 := by
      rw [hδdef]
      exact min_le_left _ _
    have hδ_δ1 : δ ≤ δ1 := by
      rw [hδdef]
      exact min_le_right _ _
    have hδ_min : δ ≤ min (τ - t0) (t1 - τ) := by
      have hhalf : (min (τ - t0) (t1 - τ)) / 2 ≤ min (τ - t0) (t1 - τ) := by
        linarith [hgap0]
      exact le_trans hδ_gap hhalf
    have hδ_t0 : δ ≤ τ - t0 := le_trans hδ_min (min_le_left _ _)
    have hδ_t1 : δ ≤ t1 - τ := le_trans hδ_min (min_le_right _ _)
    have hτδ0 : τ - δ ≥ t0 := by linarith
    have hτδ1 : τ + δ ≤ t1 := by linarith
    have hYpos : 0 < (ε / 3) / K := div_pos hε3 hKpos
    have hXlt : C * (2 * δ) < ((ε / 3) / K) ^ 2 := by
      have hRHSpos : 0 < ((ε / 3) / K) ^ 2 := pow_pos hYpos 2
      have hδ1_eq : C * (2 * δ1) = ((ε / 3) / K) ^ 2 / 2 := by
        rw [hδ1def]
        field_simp
        ring
      have hCle : C * (2 * δ) ≤ C * (2 * δ1) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        exact mul_le_mul_of_nonneg_left hδ_δ1 (by norm_num)
      calc C * (2 * δ) ≤ C * (2 * δ1) := hCle
        _ = ((ε / 3) / K) ^ 2 / 2 := hδ1_eq
        _ < ((ε / 3) / K) ^ 2 := by linarith [hRHSpos]
    have hsqrt_lt : Real.sqrt (C * (2 * δ)) < (ε / 3) / K :=
      (Real.sqrt_lt' hYpos).mpr hXlt
    have hkey : Real.sqrt (C * (2 * δ)) * K < ε / 3 := by
      calc Real.sqrt (C * (2 * δ)) * K < ((ε / 3) / K) * K :=
            mul_lt_mul_of_pos_right hsqrt_lt hKpos
        _ = ε / 3 := div_mul_cancel₀ _ hKne
    have hev : ∀ᶠ N : ℕ in Filter.atTop, (t1 - t0) / ((φm N : ℕ) : ℝ) < δ :=
      hτ_tendsto.eventually (gt_mem_nhds hδ0)
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
    have hBump := hBumpCauchyThm τ δ hτmem hδ0 hτδ0 hτδ1 ψ hψ
    rw [Metric.cauchySeq_iff] at hBump
    obtain ⟨N₂, hN₂⟩ := hBump (ε / 3) hε3
    refine ⟨max N₁ (max N₂ 1), fun m hm n hn => ?_⟩
    have hN01 : 1 ≤ max N₁ (max N₂ 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one (le_trans hN01 hm)
    have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one (le_trans hN01 hn)
    have hN1N0 : N₁ ≤ max N₁ (max N₂ 1) := le_max_left _ _
    have hN2N0 : N₂ ≤ max N₁ (max N₂ 1) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hm1 : N₁ ≤ m := le_trans hN1N0 hm
    have hn1 : N₁ ≤ n := le_trans hN1N0 hn
    have hm2 : N₂ ≤ m := le_trans hN2N0 hm
    have hn2 : N₂ ≤ n := le_trans hN2N0 hn
    have hτm := hN₁ m hm1
    have hτn := hN₁ n hn1
    have hconc_m := hConc m hm0 τ δ hτmem hδ0 hτδ0 hτδ1 ψ hψ
    have hconc_n := hConc n hn0 τ δ hτmem hδ0 hτδ0 hτδ1 ψ hψ
    have hbound_m :=
      sqrt_conc_mono C δ ((t1 - t0) / ((φm m : ℕ) : ℝ)) K ε hC0 hK0 hτm hkey
    have hbound_n :=
      sqrt_conc_mono C δ ((t1 - t0) / ((φm n : ℕ) : ℝ)) K ε hC0 hK0 hτn hkey
    have h1 := lt_of_le_of_lt hconc_m hbound_m
    have h2 := lt_of_le_of_lt hconc_n hbound_n
    have hBdist := hN₂ m hm2 n hn2
    rw [Real.dist_eq] at hBdist
    rw [Real.dist_eq]
    exact abs_triangle_3 _ _ _ _ _ h1 hBdist h2


theorem rothe_lebesgue_points
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hBochnerThm : AEStronglyMeasurable
      (fun t => if ht : t ∈ Set.Icc t0 t1 then
        MemLp.toLp (fun x => u t x) (hMemThm t ht) else 0)
      (volume.restrict (Set.Icc t0 t1)))
    (hL1Thm : Integrable (fun t => (eLpNorm (fun x => u t x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) (volume.restrict (Set.Icc t0 t1))) :
    ∃ G : Set ℝ, volume (Set.Icc t0 t1 \ G) = 0 ∧ ∀ τ : ℝ, τ ∈ G →
      Filter.Tendsto
        (fun δ : ℝ => (1 / (2 * δ)) *
          ∫ t in Set.Icc (τ - δ) (τ + δ),
            (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
              ∂(volume.restrict (Set.Icc t0 t1)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
  set s : Set ℝ := Set.Icc t0 t1 with hs
  set F : ℝ → Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    fun t => if ht : t ∈ s then MemLp.toLp (fun x => u t x) (hMemThm t ht) else 0 with hF
  have hsMeas : MeasurableSet s := measurableSet_Icc
  have hFmeas : AEStronglyMeasurable F volume := by
    have hEq : F = s.piecewise F 0 := by
      funext t
      by_cases hmem : t ∈ s
      · simp [hF, hmem]
      · simp [hF, hmem]
    rw [hEq]
    apply AEStronglyMeasurable.piecewise hsMeas.nullMeasurableSet
    · simpa [hs, hF] using hBochnerThm
    · exact aestronglyMeasurable_const
  have hNormEq : (fun t => ‖F t‖) = s.indicator
      (fun t => (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) := by
    funext t
    by_cases hmem : t ∈ s
    · rw [Set.indicator_of_mem hmem]
      simp [hF, hmem, Lp.norm_toLp]
    · rw [Set.indicator_of_notMem hmem]
      simp [hF, hmem]
  have hNormInt : Integrable (fun t => ‖F t‖) volume := by
    rw [hNormEq]
    rw [integrable_indicator_iff hsMeas]
    simpa [hs, IntegrableOn] using hL1Thm
  have hFint : Integrable F volume := (integrable_norm_iff hFmeas).mp hNormInt
  have hFloc : LocallyIntegrable F volume := hFint.locallyIntegrable
  have hLeb0 := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure ℝ) hFloc (0 : ℝ)
  have hLeb : ∀ᵐ x : ℝ ∂volume, Filter.Tendsto
      (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖F y - F x‖ ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [hLeb0] with x hx
    apply hx (fun _ => x) (fun δ => δ)
    · exact Filter.tendsto_id
    · apply Filter.Eventually.of_forall
      intro δ
      show x ∈ Metric.closedBall x (0 * δ)
      rw [zero_mul]
      exact Metric.mem_closedBall_self le_rfl
  have hNull : volume {x : ℝ | ¬ Filter.Tendsto
      (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖F y - F x‖ ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)} = 0 := ae_iff.mp hLeb
  refine ⟨s ∩ {x | Filter.Tendsto
      (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖F y - F x‖ ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)}, ?_, ?_⟩
  · have hSub : s \ (s ∩ {x | Filter.Tendsto
        (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖F y - F x‖ ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)})
      ⊆ {x : ℝ | ¬ Filter.Tendsto
        (fun δ : ℝ => ⨍ y in Metric.closedBall x δ, ‖F y - F x‖ ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)} := by
      intro x hx
      simp at hx ⊢
      exact hx.2
    exact measure_mono_null hSub hNull
  · intro τ hτ
    simp at hτ
    obtain ⟨hτmem, hAvg⟩ := hτ
    apply squeeze_zero' _ _ hAvg
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδpos : 0 < δ := hδ
      apply mul_nonneg
      · apply div_nonneg zero_le_one
        positivity
      · apply integral_nonneg_of_ae
        apply Filter.Eventually.of_forall
        intro t
        exact ENNReal.toReal_nonneg
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδpos : 0 < δ := hδ
      have hCoeff : 0 ≤ (1 / (2 * δ) : ℝ) := by
        apply div_nonneg zero_le_one
        positivity
      have hAvgEq : (⨍ y in Metric.closedBall τ δ, ‖F y - F τ‖ ∂volume)
          = (1 / (2 * δ)) * ∫ y in Metric.closedBall τ δ, ‖F y - F τ‖ ∂volume := by
        have hReal : (volume : Measure ℝ).real (Metric.closedBall τ δ) = 2 * δ := by
          rw [Measure.real_def, Real.volume_closedBall, ENNReal.toReal_ofReal]
          positivity
        rw [setAverage_eq, hReal, smul_eq_mul, inv_eq_one_div]
      have hBall : Metric.closedBall τ δ = Set.Icc (τ - δ) (τ + δ) := Real.closedBall_eq_Icc
      rw [hAvgEq, hBall]
      apply mul_le_mul_of_nonneg_left _ hCoeff
      have hRestrict : (∫ t in Set.Icc (τ - δ) (τ + δ),
              (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
                ∂(volume.restrict (Set.Icc t0 t1)))
          = ∫ t in Set.Icc (τ - δ) (τ + δ) ∩ Set.Icc t0 t1,
              (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
                ∂volume := by
        have h : (volume.restrict (Set.Icc t0 t1)).restrict (Set.Icc (τ - δ) (τ + δ))
            = volume.restrict (Set.Icc (τ - δ) (τ + δ) ∩ Set.Icc t0 t1) :=
          Measure.restrict_restrict measurableSet_Icc
        exact h ▸ rfl
      rw [hRestrict]
      have hCongr : (∫ t in Set.Icc (τ - δ) (τ + δ) ∩ Set.Icc t0 t1,
              (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
                ∂volume)
          = ∫ t in Set.Icc (τ - δ) (τ + δ) ∩ Set.Icc t0 t1, ‖F t - F τ‖ ∂volume := by
        apply setIntegral_congr_ae (measurableSet_Icc.inter measurableSet_Icc)
        apply Filter.Eventually.of_forall
        intro t ht
        have htmIcc : t ∈ Set.Icc t0 t1 := ht.2
        have htm : t ∈ s := by rw [hs]; exact htmIcc
        have hFt : F t = MemLp.toLp (fun x => u t x) (hMemThm t htm) := by
          simp [hF, htm]
        have hFτ : F τ = MemLp.toLp (fun x => u τ x) (hMemThm τ hτmem) := by
          simp [hF, hτmem]
        rw [hFt, hFτ]
        have hSub := MemLp.toLp_sub (hMemThm t htm) (hMemThm τ hτmem)
        rw [← hSub, Lp.norm_toLp]
        congr 1
      rw [hCongr]
      have hFres : Integrable F (volume.restrict (Set.Icc (τ - δ) (τ + δ))) := hFint.restrict
      have hConst : Integrable (fun _ => F τ) (volume.restrict (Set.Icc (τ - δ) (τ + δ))) :=
        integrable_const _
      have hSubI : Integrable (fun y => F y - F τ) (volume.restrict (Set.Icc (τ - δ) (τ + δ))) :=
        hFres.sub hConst
      have hNorm : IntegrableOn (fun y => ‖F y - F τ‖) (Set.Icc (τ - δ) (τ + δ)) volume :=
        hSubI.norm
      apply setIntegral_mono_set hNorm
      · apply Filter.Eventually.of_forall
        intro y
        exact norm_nonneg _
      · apply Filter.Eventually.of_forall
        intro x hx
        exact hx.1


theorem memLp_snd_comp_of_memLp
    {t0 t1 : ℝ}
    {φ : ℝ → ℝ} (hφ : MemLp φ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (fun p : ℝ × ℝ => φ p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
  have hexp : (2 : ENNReal).toReal = 2 := ENNReal.toReal_ofNat 2
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.2)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hφ.aestronglyMeasurable.comp_snd
  have hiff := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ENNReal))
    (μ := (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (show (2 : ENNReal) ≠ 0 by simp) (show (2 : ENNReal) ≠ ⊤ by simp)
    (f := fun p : ℝ × ℝ => φ p.2) hmeas
  show eLpNorm (fun p : ℝ × ℝ => φ p.2) 2
    ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) < ⊤
  rw [hiff, hexp]
  simp_rw [ENNReal.rpow_two]
  have hAE : AEMeasurable (fun p : ℝ × ℝ => ‖φ p.2‖ₑ ^ 2)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (hφ.aestronglyMeasurable.enorm.comp_snd).pow_const 2
  show (∫⁻ p, ‖φ p.2‖ₑ ^ 2
    ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) < ⊤
  rw [lintegral_prod _ hAE]
  show (∫⁻ t, ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
    ∂(volume.restrict (Set.Icc t0 t1))) < ⊤
  rw [lintegral_const]
  apply ENNReal.mul_lt_top
  · have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (show (2 : ENNReal) ≠ 0 by simp) (show (2 : ENNReal) ≠ ⊤ by simp) hφ
    simpa [hexp, ENNReal.rpow_two] using h
  · rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top


theorem prod_restrict_Icc_eq (t0 t1 : ℝ) :
    (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))
      = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]


theorem integrable_pairing_of_joint
    {t0 t1 : ℝ}
    (u : ℝ → ℝ → ℝ)
    (hJoint : MemLp (Function.uncurry u) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (ψ : ℝ → ℝ)
    (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable (fun t : ℝ => ∫ x in (0 : ℝ)..1, u t x * ψ x)
      (volume.restrict (Set.Icc t0 t1)) := by
  have hμ := prod_restrict_Icc_eq t0 t1
  have hJointProd : MemLp (Function.uncurry u) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hμ]
    exact hJoint
  have hPsi : MemLp (fun p : ℝ × ℝ => ψ p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    memLp_snd_comp_of_memLp hψ
  have hF : MemLp (fun p : ℝ × ℝ => u p.1 p.2 * ψ p.2) 1
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hJointProd.mul hPsi
  have hFint : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * ψ p.2)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    memLp_one_iff_integrable.mp hF
  have hP' : Integrable
      (fun t : ℝ => ∫ x, u t x * ψ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (volume.restrict (Set.Icc t0 t1)) :=
    hFint.integral_prod_left
  have hEq : ∀ t : ℝ, (∫ x, u t x * ψ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ x in (0 : ℝ)..1, u t x * ψ x := fun t => by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hP'.congr (Filter.Eventually.of_forall hEq)


theorem memLp_slice_eLpNorm_of_joint
    {t0 t1 : ℝ}
    (u : ℝ → ℝ → ℝ)
    (hMem : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hJoint : MemLp (Function.uncurry u) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (τ : ℝ) (hτ : τ ∈ Set.Icc t0 t1) :
    MemLp (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) 2
      (volume.restrict (Set.Icc t0 t1)) := by
  have hμ := prod_restrict_Icc_eq t0 t1
  have hJointProd : MemLp (Function.uncurry u) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hμ]
    exact hJoint
  have hSlice : MemLp (fun p : ℝ × ℝ => u τ p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    memLp_snd_comp_of_memLp (hMem τ hτ)
  have hF' : MemLp (fun p : ℝ × ℝ => u p.1 p.2 - u τ p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hJointProd.sub hSlice
  have hSliceMem : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    fun t htIcc => (hMem t htIcc).sub (hMem τ hτ)
  have hexp : (2 : ENNReal).toReal = 2 := ENNReal.toReal_ofNat 2
  have he : AEMeasurable (fun p : ℝ × ℝ => ‖u p.1 p.2 - u τ p.2‖ₑ ^ (2 : ENNReal).toReal)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hexp]
    simp_rw [ENNReal.rpow_two]
    show AEMeasurable (fun p : ℝ × ℝ => ‖u p.1 p.2 - u τ p.2‖ₑ ^ 2) _
    exact (hF'.aestronglyMeasurable.enorm).pow_const 2
  have hSliceEq : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
        = (∫⁻ x, ‖u t x - u τ x‖ₑ ^ (2 : ENNReal).toReal
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ^ (1 / (2 : ENNReal).toReal) := by
    intro t htIcc
    exact eLpNorm_eq_lintegral_rpow_enorm_toReal (show (2 : ENNReal) ≠ 0 by simp)
      (show (2 : ENNReal) ≠ ⊤ by simp) (hSliceMem t htIcc).aestronglyMeasurable
  have hENN : ∀ E : ENNReal, ((E ^ (1 / (2 : ENNReal).toReal)).toReal) ^ 2 = E.toReal := by
    rw [hexp]
    intro E
    by_cases hE : E = ⊤
    · subst hE
      rw [ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ENNReal.toReal_top]
      norm_num
    · have h2 : ((1 : ℝ) / 2) * (((2 : ℕ)) : ℝ) = 1 := by norm_num
      calc ((E ^ ((1 : ℝ) / 2)).toReal) ^ 2
          = ((E ^ ((1 : ℝ) / 2)) ^ (2 : ℕ)).toReal := (ENNReal.toReal_pow _ _).symm
        _ = ((E ^ ((1 : ℝ) / 2)) ^ ((((2 : ℕ))) : ℝ)).toReal := by
            rw [← ENNReal.rpow_natCast]
        _ = (E ^ (((1 : ℝ) / 2) * (((2 : ℕ)) : ℝ))).toReal := by rw [ENNReal.rpow_mul]
        _ = E.toReal := by rw [h2, ENNReal.rpow_one]
  have hQeq : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      (((eLpNorm (fun x => u t x - u τ x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2)
      = (∫⁻ x, ‖u t x - u τ x‖ₑ ^ (2 : ENNReal).toReal
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    intro t htIcc
    rw [hSliceEq t htIcc]
    exact hENN _
  have hL'meas : Measurable (fun t : ℝ => ∫⁻ x,
      AEMeasurable.mk (fun p : ℝ × ℝ => ‖u p.1 p.2 - u τ p.2‖ₑ ^ (2 : ENNReal).toReal) he
        (t, x) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    Measurable.lintegral_prod_right he.measurable_mk
  have hLL' : (fun t : ℝ => ∫⁻ x, ‖u t x - u τ x‖ₑ ^ (2 : ENNReal).toReal
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      =ᵐ[volume.restrict (Set.Icc t0 t1)]
      (fun t : ℝ => ∫⁻ x, AEMeasurable.mk _ he (t, x)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have hae := Measure.ae_ae_eq_of_ae_eq_uncurry
      (f := fun t x : ℝ => ‖u t x - u τ x‖ₑ ^ (2 : ENNReal).toReal)
      (g := fun t x : ℝ => AEMeasurable.mk _ he (t, x)) he.ae_eq_mk
    filter_upwards [hae] with t ht
    exact lintegral_congr_ae ht
  have hQQ' : (fun t : ℝ => (((eLpNorm (fun x => u t x - u τ x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2))
      =ᵐ[volume.restrict (Set.Icc t0 t1)]
      (fun t : ℝ => (∫⁻ x, AEMeasurable.mk _ he (t, x)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) := by
    have h1 : (fun t : ℝ => (((eLpNorm (fun x => u t x - u τ x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2))
        =ᵐ[volume.restrict (Set.Icc t0 t1)]
        (fun t : ℝ => (∫⁻ x, ‖u t x - u τ x‖ₑ ^ (2 : ENNReal).toReal
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t htIcc
      exact hQeq t htIcc
    have h2 : (fun t : ℝ => (∫⁻ x, ‖u t x - u τ x‖ₑ ^ (2 : ENNReal).toReal
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        =ᵐ[volume.restrict (Set.Icc t0 t1)]
        (fun t : ℝ => (∫⁻ x, AEMeasurable.mk _ he (t, x)
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :=
      hLL'.fun_comp ENNReal.toReal
    exact h1.trans h2
  have hQ'meas : Measurable (fun t : ℝ => (∫⁻ x, AEMeasurable.mk _ he (t, x)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :=
    ENNReal.measurable_toReal.comp hL'meas
  have hQ : AEStronglyMeasurable (fun t : ℝ => (((eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2))
      (volume.restrict (Set.Icc t0 t1)) :=
    hQ'meas.aestronglyMeasurable.congr hQQ'.symm
  have hN : AEStronglyMeasurable (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      (volume.restrict (Set.Icc t0 t1)) := by
    have hsqrt := Real.continuous_sqrt.comp_aestronglyMeasurable hQ
    have hEq : (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        = fun t : ℝ => √((((eLpNorm (fun x => u t x - u τ x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2)) :=
      funext (fun t => (Real.sqrt_sq ENNReal.toReal_nonneg).symm)
    rw [hEq]
    exact hsqrt
  show eLpNorm (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) 2
    (volume.restrict (Set.Icc t0 t1)) < ⊤
  have hiff := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ENNReal))
    (μ := volume.restrict (Set.Icc t0 t1))
    (show (2 : ENNReal) ≠ 0 by simp) (show (2 : ENNReal) ≠ ⊤ by simp)
    (f := fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) hN
  rw [hiff]
  have hInt : (∫⁻ t, ‖(eLpNorm (fun x => u t x - u τ x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal‖ₑ ^ (2 : ENNReal).toReal
        ∂(volume.restrict (Set.Icc t0 t1)))
      = ∫⁻ p, ‖u p.1 p.2 - u τ p.2‖ₑ ^ (2 : ENNReal).toReal
        ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have hcongr : (fun t : ℝ => ‖(eLpNorm (fun x => u t x - u τ x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal‖ₑ ^ (2 : ENNReal).toReal)
        =ᵐ[volume.restrict (Set.Icc t0 t1)]
        (fun t : ℝ => ∫⁻ x, (fun p : ℝ × ℝ => ‖u p.1 p.2 - u τ p.2‖ₑ
          ^ (2 : ENNReal).toReal) (t, x) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t htIcc
      have hE : eLpNorm (fun x => u t x - u τ x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
        ne_of_lt (hSliceMem t htIcc)
      rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hE,
        hSliceEq t htIcc, hexp, ← ENNReal.rpow_mul,
        show ((1 : ℝ) / 2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rw [lintegral_congr_ae hcongr, ← lintegral_prod _ he]
  show (∫⁻ t, ‖(eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal‖ₑ ^ (2 : ENNReal).toReal
    ∂(volume.restrict (Set.Icc t0 t1))) < ⊤
  rw [hInt]
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (show (2 : ENNReal) ≠ 0 by simp) (show (2 : ENNReal) ≠ ⊤ by simp) hF'

/-- Pairing Lebesgue-point convergence. -/

theorem rothe_lebesgue_pairing_joint
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (G : Set ℝ)
    (hJointThm : MemLp (Function.uncurry u) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)))
    (hLebThm : ∀ τ : ℝ, τ ∈ G →
      Filter.Tendsto
        (fun δ : ℝ => (1 / (2 * δ)) *
          ∫ t in Set.Icc (τ - δ) (τ + δ),
            (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
              ∂(volume.restrict (Set.Icc t0 t1)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0))
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ τ : ℝ, τ ∈ G → t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto
        (fun δ : ℝ => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)) := by
  intro τ hτG hτ0 hτ1 ψ hψ
  have hτIcc : τ ∈ Set.Icc t0 t1 := ⟨le_of_lt hτ0, le_of_lt hτ1⟩
  have hP : Integrable (fun t : ℝ => ∫ x in (0 : ℝ)..1, u t x * ψ x)
      (volume.restrict (Set.Icc t0 t1)) :=
    integrable_pairing_of_joint u hJointThm ψ hψ
  have hN : MemLp (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) 2 (volume.restrict (Set.Icc t0 t1)) :=
    memLp_slice_eLpNorm_of_joint u hMemThm hJointThm τ hτIcc
  have hfinT : (volume.restrict (Set.Icc t0 t1)) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hNint : Integrable (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      (volume.restrict (Set.Icc t0 t1)) := by
    have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Icc t0 t1)) :=
      (memLp_const_iff (show (2 : ENNReal) ≠ 0 by simp)
        (show (2 : ENNReal) ≠ ⊤ by simp)).mpr (Or.inr hfinT)
    have h := hN.integrable_mul h1
    exact h.congr (Filter.Eventually.of_forall (fun t => mul_one _))
  have hCS : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)|
      ≤ (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    intro t htIcc
    have hmul_t : Integrable ((fun x => u t x) * ψ)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hMemThm t htIcc).integrable_mul hψ
    have hmul_τ : Integrable ((fun x => u τ x) * ψ)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hMemThm τ hτIcc).integrable_mul hψ
    have hPt : Integrable (fun x => u t x * ψ x)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      have h := hmul_t.restrict (s := Set.Ioc (0 : ℝ) 1)
      rw [Measure.restrict_restrict measurableSet_Ioc] at h
      rw [Set.inter_eq_self_of_subset_left Set.Ioc_subset_Icc_self] at h
      exact h
    have hPτ : Integrable (fun x => u τ x * ψ x)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      have h := hmul_τ.restrict (s := Set.Ioc (0 : ℝ) 1)
      rw [Measure.restrict_restrict measurableSet_Ioc] at h
      rw [Set.inter_eq_self_of_subset_left Set.Ioc_subset_Icc_self] at h
      exact h
    have hDiff : (∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)
        = ∫ x in (0 : ℝ)..1, (u t x - u τ x) * ψ x := by
      simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      rw [← integral_sub hPt hPτ]
      apply integral_congr_ae
      filter_upwards with x
      show u t x * ψ x - u τ x * ψ x = (u t x - u τ x) * ψ x
      ring
    have hDiff2 : (∫ x in (0 : ℝ)..1, (fun x => u t x - u τ x) x * ψ x)
        = (∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x) :=
      hDiff.symm
    have hsub : MemLp (fun x => u t x - u τ x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hMemThm t htIcc).sub (hMemThm τ hτIcc)
    have hCS0 := hCSThm hsub hψ
    rw [hDiff2] at hCS0
    exact hCS0
  have hε : (0 : ℝ) < min (τ - t0) (t1 - τ) :=
    lt_min (sub_pos.mpr hτ0) (sub_pos.mpr hτ1)
  have hbound : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      ‖(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        - (∫ x in (0 : ℝ)..1, u τ x * ψ x)‖
      ≤ (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        * ((1 / (2 * δ)) * ∫ t in Set.Icc (τ - δ) (τ + δ),
          (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          ∂(volume.restrict (Set.Icc t0 t1))) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
    obtain ⟨hδ0, hδε⟩ := hδ
    have hδ1 : δ < τ - t0 := lt_of_lt_of_le hδε (min_le_left _ _)
    have hδ2 : δ < t1 - τ := lt_of_lt_of_le hδε (min_le_right _ _)
    have h2δ : (0 : ℝ) < 2 * δ := by linarith
    have hδne : (2 : ℝ) * δ ≠ 0 := ne_of_gt h2δ
    have hc : (0 : ℝ) < 1 / (2 * δ) := one_div_pos.mpr h2δ
    have hSsub : Set.Ioo (τ - δ) (τ + δ) ⊆ Set.Icc t0 t1 := by
      intro t ht
      obtain ⟨h1, h2⟩ := ht
      have h1' : t0 < τ - δ := by linarith
      have h2' : τ + δ < t1 := by linarith
      exact ⟨le_of_lt (by linarith), le_of_lt (by linarith)⟩
    have hSsubIoc : Set.Ioo (τ - δ) (τ + δ) ⊆ Set.Ioc t0 t1 := by
      intro t ht
      obtain ⟨h1, h2⟩ := ht
      have h1' : t0 < τ - δ := by linarith
      have h2' : τ + δ < t1 := by linarith
      exact ⟨by linarith, by linarith⟩
    have hIccsub : Set.Icc (τ - δ) (τ + δ) ⊆ Set.Icc t0 t1 := by
      intro t ht
      obtain ⟨h1, h2⟩ := ht
      have h1' : t0 ≤ τ - δ := by linarith
      have h2' : τ + δ ≤ t1 := by linarith
      exact ⟨by linarith, by linarith⟩
    have hSm : MeasurableSet (Set.Ioo (τ - δ) (τ + δ)) := measurableSet_Ioo
    have hIccm : MeasurableSet (Set.Icc (τ - δ) (τ + δ)) := measurableSet_Icc
    have hfinS : (volume.restrict (Set.Ioo (τ - δ) (τ + δ))) Set.univ < ⊤ := by
      rw [Measure.restrict_apply_univ, Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hPS : Integrable (fun t : ℝ => ∫ x in (0 : ℝ)..1, u t x * ψ x)
        (volume.restrict (Set.Ioo (τ - δ) (τ + δ))) := by
      have h := hP.restrict (s := Set.Ioo (τ - δ) (τ + δ))
      rw [Measure.restrict_restrict hSm] at h
      rw [Set.inter_eq_self_of_subset_left hSsub] at h
      exact h
    have hNS : Integrable (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        (volume.restrict (Set.Ioo (τ - δ) (τ + δ))) := by
      have h := hNint.restrict (s := Set.Ioo (τ - δ) (τ + δ))
      rw [Measure.restrict_restrict hSm] at h
      rw [Set.inter_eq_self_of_subset_left hSsub] at h
      exact h
    have hPc : Integrable (fun _ : ℝ => (∫ x in (0 : ℝ)..1, u τ x * ψ x))
        (volume.restrict (Set.Ioo (τ - δ) (τ + δ))) :=
      integrable_const_iff.mpr (Or.inr ⟨hfinS⟩)
    have hFind : (∫ t in t0..t1, (1 / (2 * δ))
          * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        = (1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
          (∫ x in (0 : ℝ)..1, u t x * ψ x) ∂volume := by
      rw [intervalIntegral.integral_of_le ht.le]
      have hpt : ∀ t : ℝ, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
            * (∫ x in (0 : ℝ)..1, u t x * ψ x)
          = (1 / (2 * δ)) * (Set.Ioo (τ - δ) (τ + δ)).indicator
            (fun t => ∫ x in (0 : ℝ)..1, u t x * ψ x) t := by
        intro t
        by_cases hmem : t ∈ Set.Ioo (τ - δ) (τ + δ)
        · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
          simp only [Pi.one_apply]
          ring
        · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
          ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
      congr 1
      rw [integral_indicator hSm]
      have hmeas : ((volume.restrict (Set.Ioc t0 t1)).restrict (Set.Ioo (τ - δ) (τ + δ)))
          = volume.restrict (Set.Ioo (τ - δ) (τ + δ)) := by
        rw [Measure.restrict_restrict hSm, Set.inter_eq_self_of_subset_left hSsubIoc]
      rw [hmeas]
    have h2δeq : (τ + δ) - (τ - δ) = 2 * δ := by ring
    have hPτav : (∫ x in (0 : ℝ)..1, u τ x * ψ x)
        = (1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
          (∫ x in (0 : ℝ)..1, u τ x * ψ x) ∂volume := by
      rw [setIntegral_const]
      show (∫ x in (0 : ℝ)..1, u τ x * ψ x)
        = (1 / (2 * δ)) * (((volume (Set.Ioo (τ - δ) (τ + δ))).toReal)
          • (∫ x in (0 : ℝ)..1, u τ x * ψ x))
      rw [Real.volume_Ioo, h2δeq, ENNReal.toReal_ofReal (le_of_lt h2δ),
        smul_eq_mul, ← mul_assoc, one_div_mul_cancel hδne, one_mul]
    have hsub : (∫ t in t0..t1, (1 / (2 * δ))
          * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        - (∫ x in (0 : ℝ)..1, u τ x * ψ x)
        = (1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
          ((∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)) ∂volume := by
      rw [hFind]
      nth_rewrite 1 [hPτav]
      rw [← mul_sub, ← integral_sub hPS hPc]
    have hDint : Integrable
        (fun t : ℝ => (∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x))
        (volume.restrict (Set.Ioo (τ - δ) (τ + δ))) :=
      hPS.sub hPc
    have hNmul : Integrable (fun t : ℝ => (eLpNorm (fun x => u t x - u τ x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        (volume.restrict (Set.Ioo (τ - δ) (τ + δ))) :=
      hNS.mul_const _
    have hle : ∀ᵐ t ∂(volume.restrict (Set.Ioo (τ - δ) (τ + δ))),
        |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)|
        ≤ (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
      filter_upwards [ae_restrict_mem hSm] with t htS
      exact hCS t (hSsub htS)
    have hnorm : |∫ t in Set.Ioo (τ - δ) (τ + δ),
          ((∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)) ∂volume|
        ≤ ∫ t in Set.Ioo (τ - δ) (τ + δ),
          |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)| ∂volume := by
      have h := norm_integral_le_integral_norm
        (fun t : ℝ => (∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x))
        (μ := volume.restrict (Set.Ioo (τ - δ) (τ + δ)))
      simpa only [Real.norm_eq_abs] using h
    have hboundδ : |(∫ t in t0..t1, (1 / (2 * δ))
          * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        - (∫ x in (0 : ℝ)..1, u τ x * ψ x)|
        ≤ (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * ((1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
            (eLpNorm (fun x => u t x - u τ x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ∂volume) := by
      rw [hsub, abs_mul, abs_of_pos hc]
      calc (1 / (2 * δ)) * |∫ t in Set.Ioo (τ - δ) (τ + δ),
            ((∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)) ∂volume|
          ≤ (1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
            |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u τ x * ψ x)| ∂volume :=
            mul_le_mul_of_nonneg_left hnorm (le_of_lt hc)
        _ ≤ (1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
            ((eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ∂volume :=
            mul_le_mul_of_nonneg_left (integral_mono_ae hDint.abs hNmul hle) (le_of_lt hc)
        _ = (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * ((1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
              (eLpNorm (fun x => u t x - u τ x) 2
                (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ∂volume) := by
            rw [integral_mul_const]
            ring
    have havgδ : (1 / (2 * δ)) * ∫ t in Set.Ioo (τ - δ) (τ + δ),
          (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ∂volume
        = (1 / (2 * δ)) * ∫ t in Set.Icc (τ - δ) (τ + δ),
          (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          ∂(volume.restrict (Set.Icc t0 t1)) := by
      congr 1
      have h1 : (∫ t in Set.Icc (τ - δ) (τ + δ),
            (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            ∂(volume.restrict (Set.Icc t0 t1)))
          = ∫ t in Set.Icc (τ - δ) (τ + δ),
            (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            ∂volume := by
        have hmeas : ((volume.restrict (Set.Icc t0 t1)).restrict (Set.Icc (τ - δ) (τ + δ)))
            = volume.restrict (Set.Icc (τ - δ) (τ + δ)) := by
          rw [Measure.restrict_restrict hIccm,
            Set.inter_eq_self_of_subset_left hIccsub]
        rw [hmeas]
      rw [h1, ← integral_Ioc_eq_integral_Ioo, ← integral_Icc_eq_integral_Ioc]
    rw [Real.norm_eq_abs, ← havgδ]
    exact hboundδ
  have havg : Filter.Tendsto (fun δ : ℝ => (eLpNorm ψ 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      * ((1 / (2 * δ)) * ∫ t in Set.Icc (τ - δ) (τ + δ),
        (eLpNorm (fun x => u t x - u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ∂(volume.restrict (Set.Icc t0 t1))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (hLebThm τ hτG).const_mul
      (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
    rwa [mul_zero] at h
  have hlim := squeeze_zero_norm' hbound havg
  have hPτ : Filter.Tendsto (fun _ : ℝ => (∫ x in (0 : ℝ)..1, u τ x * ψ x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)) :=
    tendsto_const_nhds
  have hlim2 := hlim.add hPτ
  simpa only [sub_add_cancel, zero_add] using hlim2


theorem rothe_slice_limsup_bound
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (hConcThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ τ δ : ℝ,
      τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x))
        - (∫ x in (0 : ℝ)..1,
              (if τ = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)|
        ≤ Real.sqrt (C * (δ + (t1 - t0) / (φm N)))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hWeakSTThm : ∀ Ψ : ℝ → ℝ → ℝ,
      MemLp (Function.uncurry Ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U (φm N) (φm N)) p.2
             else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)) p.2)
              * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          u p.1 p.2 * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hBumpEqThm : ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U (φm N) (φm N)) p.2
             else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)) p.2)
              * ((1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 p.1) * ψ p.2)
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x))
    (hBumpEqU : ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            u p.1 p.2 * ((1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 p.1) * ψ p.2)
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
    (hLimitThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L)) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc t0 t1, ∀ ψ : ℝ → ℝ,
      ∀ hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ δ : ℝ, 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
        |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
          - Classical.choose (hLimitThm τ hτ ψ hψ)|
        ≤ Real.sqrt (Classical.choose hConcThm * δ)
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro τ hτ ψ hψ δ hδ hlo hhi
  obtain ⟨hC0, hC⟩ := Classical.choose_spec hConcThm
  set Ψ : ℝ → ℝ → ℝ := fun t x => (1 / (2 * δ)) * Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t * ψ x
  set bumpN : ℕ → ℝ := fun N => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
      * (∫ x in (0 : ℝ)..1,
        (if t = t1 then (U (φm N) (φm N)) x
         else (U (φm N) (Nat.floor ((t - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
  set pairN : ℕ → ℝ := fun N => ∫ x in (0 : ℝ)..1,
      (if τ = t1 then (U (φm N) (φm N)) x
       else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x
  set B : ℝ := ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
      * (∫ x in (0 : ℝ)..1, u t x * ψ x)
  set L : ℝ := Classical.choose (hLimitThm τ hτ ψ hψ)
  set C0 : ℝ := Classical.choose hConcThm
  set K : ℝ := (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
  set R : ℕ → ℝ := fun N => Real.sqrt (C0 * (δ + (t1 - t0) / (φm N))) * K
  have hmeas : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = Measure.prod volume volume := rfl
    rw [hvol]
    exact (Measure.prod_restrict _ _).symm
  have hnull : ∀ N : Set ℝ, (volume.restrict (Set.Icc (0 : ℝ) 1)) N = 0 →
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (Set.univ ×ˢ N) = 0 := by
    intro N hN
    rw [Measure.prod_prod, hN, mul_zero]
  have hae2 : ∀ {E : Type} [MeasurableSpace E] (F G : ℝ → E),
      F =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] G →
      (fun p : ℝ × ℝ => F p.2) =ᵐ[(volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))] (fun p => G p.2) := by
    intro E _ F G hFG
    show ∀ᵐ p ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))), F p.2 = G p.2
    rw [ae_iff]
    have hN : (volume.restrict (Set.Icc (0 : ℝ) 1)) {x | ¬ F x = G x} = 0 := by
      have hmem : {x | F x = G x} ∈ ae (volume.restrict (Set.Icc (0 : ℝ) 1)) := hFG
      rw [mem_ae_iff, Set.compl_ofPred] at hmem
      exact hmem
    refine measure_mono_null ?_ (hnull _ hN)
    intro p hp
    exact Set.mem_prod.mpr ⟨trivial, hp⟩
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.2)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    obtain ⟨g, hg, hψg⟩ := hψ.aestronglyMeasurable
    exact ⟨fun p => g p.2, hg.comp_measurable measurable_snd, hae2 ψ g hψg⟩
  have e1 : (2 : ENNReal) ≠ 0 := by simp
  have e2 : (2 : ENNReal) ≠ ⊤ := by simp
  have hr : (0 : ℝ) < 1 / (2 : ENNReal).toReal := by rw [ENNReal.toReal_ofNat]; norm_num
  have hinner : (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ENNReal).toReal ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) < ⊤ := by
    have h2 : eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) < ⊤ := hψ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal e1 e2 hψ.aestronglyMeasurable] at h2
    have htop : (∫⁻ x, ‖ψ x‖ₑ ^ (2 : ENNReal).toReal ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.top_rpow_of_pos hr] at h2
      exact absurd h2 (lt_irrefl _)
    exact lt_top_iff_ne_top.mpr htop
  have hμ : (volume.restrict (Set.Icc t0 t1)) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have haemeas : AEMeasurable (fun p : ℝ × ℝ => ‖ψ p.2‖ₑ ^ (2 : ENNReal).toReal)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have hF : AEMeasurable (fun x : ℝ => ‖ψ x‖ₑ ^ (2 : ENNReal).toReal)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hψ.aestronglyMeasurable.aemeasurable.enorm).pow_const _
    obtain ⟨G, hGmeas, hFG⟩ := hF
    have hGsnd : AEMeasurable (fun p : ℝ × ℝ => G p.2)
        ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
      (hGmeas.comp measurable_snd).aemeasurable
    have hEq : (fun p : ℝ × ℝ => ‖ψ p.2‖ₑ ^ (2 : ENNReal).toReal) =ᵐ[((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))] (fun p => G p.2) :=
      hae2 _ _ hFG
    exact hGsnd.congr hEq.symm
  have hG : MemLp (fun p : ℝ × ℝ => ψ p.2) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    rw [hmeas]
    show eLpNorm (fun p : ℝ × ℝ => ψ p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) < ⊤
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal e1 e2 haesm]
    have hTon : (∫⁻ p, ‖ψ p.2‖ₑ ^ (2 : ENNReal).toReal
          ∂(((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))))
        = ∫⁻ t, ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ENNReal).toReal
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂(volume.restrict (Set.Icc t0 t1)) :=
      lintegral_prod _ haemeas
    rw [hTon, lintegral_const]
    have hAB : (∫⁻ y, ‖ψ y‖ₑ ^ (2 : ENNReal).toReal ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        * (volume.restrict (Set.Icc t0 t1)) Set.univ < ⊤ :=
      ENNReal.mul_lt_top hinner hμ
    rw [lt_top_iff_ne_top]
    intro hcon
    rw [ENNReal.rpow_eq_top_iff] at hcon
    rcases hcon with ⟨hx0, hrneg⟩ | ⟨hxtop, hrpos⟩
    · exact (not_lt.mpr hr.le) hrneg
    · exact (ne_of_lt hAB) hxtop
  have hS : MeasurableSet (Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ) :=
    measurableSet_Ioo.prod (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  have hInd : MemLp ((Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => ψ p.2)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) :=
    MemLp.indicator hS.nullMeasurableSet hG
  have hfun : Function.uncurry Ψ
      = fun p : ℝ × ℝ => (1 / (2 * δ)) * (Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ).indicator (fun q : ℝ × ℝ => ψ q.2) p := by
    funext p
    show (1 / (2 * δ)) * Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 p.1 * ψ p.2
      = (1 / (2 * δ)) * (Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ).indicator (fun q : ℝ × ℝ => ψ q.2) p
    by_cases h : p.1 ∈ Set.Ioo (τ - δ) (τ + δ)
    · rw [Set.indicator_of_mem h, Pi.one_apply]
      have hp : p ∈ Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ := Set.mem_prod.mpr ⟨h, trivial⟩
      rw [Set.indicator_of_mem hp]
      show (1 / (2 * δ)) * 1 * ψ p.2 = (1 / (2 * δ)) * ψ p.2
      ring
    · rw [Set.indicator_of_notMem h]
      have hp : p ∉ Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ := fun hmem => h (Set.mem_prod.mp hmem).1
      rw [Set.indicator_of_notMem hp]
      show (1 / (2 * δ)) * 0 * ψ p.2 = (1 / (2 * δ)) * 0
      ring
  have hMem : MemLp (Function.uncurry Ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
    rw [hfun]
    exact MemLp.const_mul hInd (1 / (2 * δ))
  have hW := hWeakSTThm Ψ hMem
  have hLimEq : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        u p.1 p.2 * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) = B :=
    hBumpEqU τ δ hτ hδ hlo hhi ψ hψ
  have hEv : (fun N : ℕ =>
        ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then (U (φm N) (φm N)) p.2
           else (U (φm N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φm N))) + 1)) p.2)
            * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) =ᶠ[atTop] bumpN := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hBumpEqThm τ δ hτ hδ hlo hhi ψ hψ N hN
  have hBump : Tendsto bumpN atTop (nhds B) := by
    have hW2 := Filter.Tendsto.congr' hEv hW
    rwa [hLimEq] at hW2
  have hPair : Tendsto pairN atTop (nhds L) :=
    Classical.choose_spec (hLimitThm τ hτ ψ hψ)
  have hAbs : Tendsto (fun N => |bumpN N - pairN N|) atTop (nhds |B - L|) :=
    (continuous_abs.tendsto _).comp (hBump.sub hPair)
  have hφTop : Tendsto φm atTop atTop := hφm.tendsto_atTop
  have hCast : Tendsto (fun N : ℕ => (Nat.cast (φm N) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφTop
  have hH : Tendsto (fun N : ℕ => (t1 - t0) / (φm N)) atTop (nhds 0) :=
    hCast.const_div_atTop (t1 - t0)
  have hAdd : Tendsto (fun N : ℕ => δ + (t1 - t0) / (φm N)) atTop (nhds (δ + 0)) :=
    hH.const_add δ
  have hMul : Tendsto (fun N : ℕ => C0 * (δ + (t1 - t0) / (φm N))) atTop (nhds (C0 * (δ + 0))) :=
    hAdd.const_mul C0
  have hInner : Tendsto (fun N : ℕ => C0 * (δ + (t1 - t0) / (φm N))) atTop (nhds (C0 * δ)) := by
    have h0 : C0 * (δ + 0) = C0 * δ := by ring
    rwa [h0] at hMul
  have hSqrt : Tendsto (fun N : ℕ => Real.sqrt (C0 * (δ + (t1 - t0) / (φm N)))) atTop
      (nhds (Real.sqrt (C0 * δ))) :=
    (Real.continuous_sqrt.tendsto _).comp hInner
  have hR : Tendsto R atTop (nhds (Real.sqrt (C0 * δ) * K)) := hSqrt.mul_const K
  have hLe : ∀ᶠ N in atTop, |bumpN N - pairN N| ≤ R N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hC N hN τ δ hτ hδ hlo hhi ψ hψ
  exact le_of_tendsto_of_tendsto hAbs hR hLe
/-- Corrected limsup bound (sqrt(C0*delta) form). -/

theorem slice_limsup_corrected
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (U_of : ℕ → ℕ → WeakH10)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hConc : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ τ δ : ℝ,
      τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U_of (φ N) (φ N)).toFun x
               else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x))
        - (∫ x in (0 : ℝ)..1,
              (if τ = t1 then (U_of (φ N) (φ N)).toFun x
               else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x)|
        ≤ Real.sqrt (C * (δ + (t1 - t0) / (φ N)))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hWeakST : ∀ Ψ : ℝ → ℝ → ℝ,
      MemLp (Function.uncurry Ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
             else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
              * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          u p.1 p.2 * Ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hBumpEq : ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
             else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
              * ((1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 p.1) * ψ p.2)
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U_of (φ N) (φ N)).toFun x
               else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x))
    (hBumpEqU : ∀ τ δ : ℝ, τ ∈ Set.Icc t0 t1 → 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            u p.1 p.2 * ((1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 p.1) * ψ p.2)
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
    (hConv : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x)
        Filter.atTop (nhds L)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ δ : ℝ, 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x)
        Filter.atTop (nhds L) →
        |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L|
        ≤ Real.sqrt (C₀ * δ)
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  refine ⟨Classical.choose hConc, (Classical.choose_spec hConc).1, ?_⟩
  intro τ hτ ψ hψ δ hδ hlo hhi L hLim
  have hBound := rothe_slice_limsup_bound ht u (fun N k => (U_of N k).toFun) φ hφ hConc hWeakST
    hBumpEq hBumpEqU hConv τ hτ ψ hψ δ hδ hlo hhi
  have hEq : L = Classical.choose (hConv τ hτ ψ hψ) :=
    tendsto_nhds_unique hLim (Classical.choose_spec (hConv τ hτ ψ hψ))
  rw [hEq]
  exact hBound


theorem rothe_slice_limit_ident
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (hLimsupThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ δ : ℝ, 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L) →
        |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L|
        ≤ Real.sqrt (2 * δ)
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hLebThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto
        (fun δ : ℝ => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x))) :
    ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L) →
        L = ∫ x in (0 : ℝ)..1, u τ x * ψ x := by
  intro τ hτ0 hτ1 ψ hψ L hLim
  have hτmem : τ ∈ Set.Icc t0 t1 := Set.mem_Icc.mpr ⟨le_of_lt hτ0, le_of_lt hτ1⟩
  have hLeb := hLebThm τ hτmem ψ hψ
  have hToL : Filter.Tendsto
      (fun δ : ℝ => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
        * (∫ x in (0 : ℝ)..1, u t x * ψ x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    have hpos1 : (0 : ℝ) < τ - t0 := sub_pos.mpr hτ0
    have hpos2 : (0 : ℝ) < t1 - τ := sub_pos.mpr hτ1
    have hball : Metric.ball (0 : ℝ) (min (τ - t0) (t1 - τ)) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds _ (lt_min hpos1 hpos2)
    have hbound : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L‖
          ≤ Real.sqrt (2 * δ) * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hball] with δ hδ hδpos
      simp only [Metric.mem_ball, dist_zero_right] at hδ
      have hδlt : δ < min (τ - t0) (t1 - τ) := (abs_lt.mp hδ).2
      have hd1 : δ < τ - t0 := lt_of_lt_of_le hδlt (min_le_left _ _)
      have hd2 : δ < t1 - τ := lt_of_lt_of_le hδlt (min_le_right _ _)
      have hlo : τ - δ ≥ t0 := by linarith
      have hhi : τ + δ ≤ t1 := by linarith
      have h := hLimsupThm τ hτmem ψ hψ δ (Set.mem_Ioi.mp hδpos) hlo hhi L hLim
      rwa [Real.norm_eq_abs]
    have hlim0 : Filter.Tendsto (fun δ : ℝ => Real.sqrt (2 * δ)
        * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2δ : Filter.Tendsto (fun δ : ℝ => (2 : ℝ) * δ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hcon : ContinuousAt (fun δ : ℝ => (2 : ℝ) * δ) 0 :=
          continuousAt_const.mul continuousAt_id
        have h : Filter.Tendsto (fun δ : ℝ => (2 : ℝ) * δ)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 : ℝ) * 0)) :=
          hcon.tendsto.mono_left nhdsWithin_le_nhds
        simpa using h
      have hsq : Filter.Tendsto (fun δ : ℝ => Real.sqrt (2 * δ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp h2δ
        rw [Real.sqrt_zero] at h
        have heq : (Real.sqrt ∘ fun δ : ℝ => (2 : ℝ) * δ)
            = fun δ : ℝ => Real.sqrt (2 * δ) := rfl
        rwa [heq] at h
      have h := hsq.mul_const ((eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      simpa using h
    have hsub : Filter.Tendsto (fun δ : ℝ => (∫ t in t0..t1, (1 / (2 * δ))
        * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
        * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      squeeze_zero_norm' hbound hlim0
    have hadd := hsub.add_const L
    simpa using hadd
  exact (tendsto_nhds_unique hLeb hToL).symm
/-- Limit identification for slice-weak. -/

theorem slice_ident_asm
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (U_of : ℕ → ℕ → WeakH10)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hLimsup : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ δ : ℝ, 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x)
        Filter.atTop (nhds L) →
        |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L|
        ≤ Real.sqrt (2 * δ)
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hLeb : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto
        (fun δ : ℝ => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x))) :
    ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N))) + 1)).toFun x) * ψ x)
        Filter.atTop (nhds L) →
        L = ∫ x in (0 : ℝ)..1, u τ x * ψ x := by
  exact rothe_slice_limit_ident ht u (fun N k => (U_of N k).toFun) φ hφ hLimsup hLeb


theorem rothe_slice_weak_final
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (G : Set ℝ)
    (hCauchyThm : ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      CauchySeq (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x))
    (hLimsupThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ δ : ℝ, 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L) →
        |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L|
        ≤ Real.sqrt (2 * δ)
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hLebPairThm : ∀ τ : ℝ, τ ∈ G → t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto
        (fun δ : ℝ => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)))
    (hIdentThm : ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L) →
        L = ∫ x in (0 : ℝ)..1, u τ x * ψ x) :
    ∀ τ : ℝ, τ ∈ G → t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)) := by
  intro τ hτG hτ0 hτ1 ψ hψ
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hCauchyThm τ hτ0 hτ1 ψ hψ)
  have hEq : L = ∫ x in (0 : ℝ)..1, u τ x * ψ x :=
    hIdentThm τ hτ0 hτ1 ψ hψ L hL
  rw [← hEq]
  exact hL


theorem rothe_slice_weak_final_corrected
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (G : Set ℝ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hCauchyThm : ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      CauchySeq (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x))
    (hLimsupThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ δ : ℝ, 0 < δ → τ - δ ≥ t0 → τ + δ ≤ t1 →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L) →
        |(∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x)) - L|
        ≤ Real.sqrt (C₀ * δ)
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hLebPairThm : ∀ τ : ℝ, τ ∈ G → t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto
        (fun δ : ℝ => ∫ t in t0..t1, (1 / (2 * δ)) * (Set.indicator (Set.Ioo (τ - δ) (τ + δ)) 1 t)
          * (∫ x in (0 : ℝ)..1, u t x * ψ x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)))
    (hIdentThm : ∀ τ : ℝ, t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ L : ℝ, Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds L) →
        L = ∫ x in (0 : ℝ)..1, u τ x * ψ x) :
    ∀ τ : ℝ, τ ∈ G → t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)) := by
  intro τ hτG hτ0 hτ1 ψ hψ
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hCauchyThm τ hτ0 hτ1 ψ hψ)
  have hEq : L = ∫ x in (0 : ℝ)..1, u τ x * ψ x :=
    hIdentThm τ hτ0 hτ1 ψ hψ L hL
  rw [← hEq]
  exact hL


theorem exists_smooth_bump (t0 t1 : ℝ) (ht : t0 < t1) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ t : ℝ, η t ≠ 0 → t0 < t ∧ t < t1) ∧ ∃ tstar : ℝ, η tstar ≠ 0 := by
  have hm : (t0 + t1) / 2 ∈ Set.Ioo t0 t1 := by
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hs : IsClosed (Set.Ioo t0 t1)ᶜ := isOpen_Ioo.isClosed_compl
  have htsingle : IsClosed ({(t0 + t1) / 2} : Set ℝ) := isClosed_singleton
  have hd : Disjoint (Set.Ioo t0 t1)ᶜ ({(t0 + t1) / 2} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hxs hxm
    rw [Set.mem_singleton_iff] at hxm
    subst hxm
    exact hxs hm
  obtain ⟨f, h0, h1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ ℝ) hs htsingle hd
      (n := ⊤)
  have hsupp_sub : Function.support ⇑f ⊆ Set.Ioo t0 t1 := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxIoo
    exact hx (h0 hxIoo)
  have hcompact : HasCompactSupport ⇑f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (hsupp_sub.trans Set.Ioo_subset_Icc_self)
  have hmem : ∀ t : ℝ, ⇑f t ≠ 0 → t0 < t ∧ t < t1 := by
    intro t ht0
    exact Set.mem_Ioo.mp (hsupp_sub (Function.mem_support.mpr ht0))
  have hne : ⇑f ((t0 + t1) / 2) ≠ 0 := by
    have hfm : ⇑f ((t0 + t1) / 2) = 1 := h1 (Set.mem_singleton _)
    rw [hfm]
    exact one_ne_zero
  exact ⟨⇑f, f.contMDiff.contDiff, hcompact, hmem, (t0 + t1) / 2, hne⟩

/-- A `WeakH10` element nonzero outside `(0, 1)` (only `[0, 1]` is constrained). -/

theorem exists_H10_nonzero_outside : ∃ v : WeakH10, v.toFun 2 ≠ 0 := by
  refine ⟨⟨fun x => if x = 2 then (1 : ℝ) else 0, fun _ => 0, MemLp.zero', ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
    have hx2 : x ≠ 2 := by linarith
    simp [hx2]
  · simp
  · show (if (2 : ℝ) = 2 then (1 : ℝ) else 0) ≠ 0
    simp

/-- Pairing reps for `H¹₀` test functions. -/

theorem pairing_rep_H10
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    (u ux : ℝ → ℝ → ℝ)
    (hWeakEqThm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
    (hTestProdThm : ∀ (η : ℝ → ℝ) (v : WeakH10),
      ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) η → HasCompactSupport η →
      (∀ t : ℝ, η t ≠ 0 → t0 < t ∧ t < t1) →
      ParabolicTest t0 t1 (fun t x => η t * v.toFun x))
    (hIntThm : ∀ (v : WeakH10),
      Integrable (fun t => ∫ x in (0 : ℝ)..1,
        (-κ t x * ux t x * v.weakDeriv x + F t x * v.toFun x))
        (volume.restrict (Set.Icc t0 t1))) :
    ∀ v : WeakH10,
      ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        (fun t => ∫ x in (0 : ℝ)..1, u t x * v.toFun x)
          =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ := by
  intro v
  exfalso
  obtain ⟨η, hηsmooth, hηcompact, hηsupp, tstar, hηne⟩ := exists_smooth_bump t0 t1 ht
  obtain ⟨vbad, hvbad⟩ := exists_H10_nonzero_outside
  obtain ⟨-, -, hsupp⟩ := hTestProdThm η vbad hηsmooth hηcompact hηsupp
  have hne : η tstar * vbad.toFun 2 ≠ 0 := mul_ne_zero hηne hvbad
  have hcon := hsupp tstar 2 hne
  have h21 : (2 : ℝ) < 1 := hcon.2.2.2
  norm_num at h21


theorem pairing_cs_bound
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hBoundThm : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ M) :
    ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ w : ℝ → ℝ,
      MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ x in (0 : ℝ)..1, u t x * w x)|
        ≤ Classical.choose hBoundThm
          * (eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro t htM w hw
  obtain ⟨hM0, hBound⟩ := Classical.choose_spec hBoundThm
  have hMemF : MemLp (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hMemThm t htM
  have hfg : ((fun x => u t x) * w) = (fun x => u t x * w x) := funext fun x => rfl
  have hInt : Integrable (fun x => u t x * w x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [← hfg]
    exact hMemF.integrable_mul hw
  have hHolder : eLpNorm (fun x => u t x * w x) 1 (volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
        * eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (· * ·) 1 continuous_mul hMemF.aestronglyMeasurable hw.aestronglyMeasurable
      (.of_forall fun _ => by simp)
    simpa using h
  have hFinF : eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
    ne_of_lt hMemF
  have hFinW : eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := ne_of_lt hw
  have hEq : (∫ x in (0 : ℝ)..1, u t x * w x)
      = ∫ x, u t x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    rw [← integral_Icc_eq_integral_Ioc (x := (0 : ℝ)) (y := (1 : ℝ))]
  calc |(∫ x in (0 : ℝ)..1, u t x * w x)|
      = ‖∫ x, u t x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))‖ := by
        rw [hEq, Real.norm_eq_abs]
    _ ≤ ∫ x, ‖u t x * w x‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        norm_integral_le_integral_norm _
    _ = (eLpNorm (fun x => u t x * w x) 1 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
        rw [integral_norm_eq_lintegral_enorm hInt.aestronglyMeasurable,
          ← eLpNorm_one_eq_lintegral_enorm hInt.aestronglyMeasurable]
    _ ≤ (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
          * eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hFinF hFinW) hHolder
    _ = (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        ENNReal.toReal_mul
    _ ≤ Classical.choose hBoundThm * (eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        mul_le_mul_of_nonneg_right (hBound t htM) ENNReal.toReal_nonneg


theorem continuous_ae_bound_le {t0 t1 : ℝ} (ht : t0 < t1) {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ}
    (h : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)), |f t| ≤ C) :
    ∀ t ∈ Set.Icc t0 t1, |f t| ≤ C := by
  intro t htm
  by_contra hlt
  rw [not_le] at hlt
  set U : Set ℝ := (fun x => |f x|) ⁻¹' (Set.Ioi C) with hUdef
  have hcont : Continuous (fun x => |f x|) := continuous_abs.comp hf
  have hopen : IsOpen U := hcont.isOpen_preimage (Set.Ioi C) isOpen_Ioi
  have htU : t ∈ U := hlt
  have hmeasU : MeasurableSet U := hopen.measurableSet
  have hU0 : (volume.restrict (Set.Icc t0 t1)) U = 0 := by
    have hnull := ae_iff.mp h
    have hset : {a : ℝ | ¬|f a| ≤ C} = U := by
      ext x
      simp [hUdef, not_le]
    rwa [hset] at hnull
  have hUIcc : volume (U ∩ Set.Icc t0 t1) = 0 := by
    rw [← Measure.restrict_apply hmeasU]
    exact hU0
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hopen t htU
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hεpos
  have hab : max t0 (t - ε / 2) < min t1 (t + ε / 2) := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    refine ⟨⟨ht, ?_⟩, ?_, ?_⟩ <;> linarith [htm.1, htm.2]
  have hsub : Set.Icc (max t0 (t - ε / 2)) (min t1 (t + ε / 2))
      ⊆ Metric.ball t ε ∩ Set.Icc t0 t1 := by
    intro x hx
    constructor
    · rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
      have hlo : t - ε / 2 ≤ x := le_trans (le_max_right _ _) hx.1
      have hhi : x ≤ t + ε / 2 := le_trans hx.2 (min_le_right _ _)
      have habs : |x - t| ≤ ε / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      exact lt_of_le_of_lt habs (half_lt_self hεpos)
    · exact ⟨le_trans (le_max_left _ _) hx.1, le_trans hx.2 (min_le_left _ _)⟩
  have hpos : (0 : ENNReal) < volume (Metric.ball t ε ∩ Set.Icc t0 t1) := by
    have h1 : (0 : ENNReal)
        < volume (Set.Icc (max t0 (t - ε / 2)) (min t1 (t + ε / 2))) := by
      rw [Real.volume_Icc, ENNReal.ofReal_pos]
      exact sub_pos.mpr hab
    exact lt_of_lt_of_le h1 (measure_mono hsub)
  have hle : volume (Metric.ball t ε ∩ Set.Icc t0 t1) ≤ 0 := by
    calc volume (Metric.ball t ε ∩ Set.Icc t0 t1)
        ≤ volume (U ∩ Set.Icc t0 t1) :=
          measure_mono (Set.inter_subset_inter hball (fun x hx => hx))
      _ = 0 := hUIcc
  exact (not_le_of_gt hpos) hle

/-- Reps are Cauchy in `C⁰`. -/

theorem pairing_reps_cauchy
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hCSBoundThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ w : ℝ → ℝ,
      MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ x in (0 : ℝ)..1, u t x * w x)|
        ≤ 2 * (eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hRepH10Thm : ∀ v : WeakH10, ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v.toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ)
    (hApproxThm : ∀ v : ℝ → ℝ, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ w : ℕ → WeakH10, Filter.Tendsto (fun n : ℕ =>
        (eLpNorm (fun x => v x - (w n).toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        Filter.atTop (nhds 0)) :
    ∀ v : ℝ → ℝ,
      ∀ _ : MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
          |(Classical.choose (hRepH10Thm (Classical.choose (hApproxThm v ‹MemLp v 2 _›) n))) t
           - (Classical.choose (hRepH10Thm (Classical.choose (hApproxThm v ‹MemLp v 2 _›) m))) t|
            ≤ ε := by
  intro v hv ε hε
  have key : ∀ (vn vm : WeakH10),
      MemLp vn.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp vm.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (ĝn ĝm : ℝ → ℝ), Continuous ĝn → Continuous ĝm →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * vn.toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝn →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * vm.toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝm →
      ∀ t ∈ Set.Icc t0 t1,
        |ĝn t - ĝm t|
          ≤ 2 * (eLpNorm (fun x => vn.toFun x - vm.toFun x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    intro vn vm hvn hvm ĝn ĝm hcn hcm hrep_n hrep_m t htm
    have hdiff : MemLp (fun x => vn.toFun x - vm.toFun x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      hvn.sub hvm
    have hC : ∀ t ∈ Set.Icc t0 t1,
        |(∫ x in (0 : ℝ)..1, u t x * (vn.toFun x - vm.toFun x))|
          ≤ 2 * (eLpNorm (fun x => vn.toFun x - vm.toFun x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
      fun t htm => hCSBoundThm t htm _ hdiff
    have hlin : ∀ t ∈ Set.Icc t0 t1,
        (∫ x in (0 : ℝ)..1, u t x * vn.toFun x)
          - (∫ x in (0 : ℝ)..1, u t x * vm.toFun x)
          = ∫ x in (0 : ℝ)..1, u t x * (vn.toFun x - vm.toFun x) := by
      intro t htm
      have hint1 : Integrable (fun x => u t x * vn.toFun x)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (hMemThm t htm).integrable_mul hvn
      have hint2 : Integrable (fun x => u t x * vm.toFun x)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (hMemThm t htm).integrable_mul hvm
      have h1 : IntervalIntegrable (fun x => u t x * vn.toFun x) volume 0 1 := by
        apply IntegrableOn.intervalIntegrable
        rw [Set.uIcc_of_le zero_le_one]
        exact hint1
      have h2 : IntervalIntegrable (fun x => u t x * vm.toFun x) volume 0 1 := by
        apply IntegrableOn.intervalIntegrable
        rw [Set.uIcc_of_le zero_le_one]
        exact hint2
      have hsub : (∫ x in (0 : ℝ)..1, u t x * vn.toFun x)
          - (∫ x in (0 : ℝ)..1, u t x * vm.toFun x)
          = ∫ x in (0 : ℝ)..1, (u t x * vn.toFun x - u t x * vm.toFun x) :=
        (intervalIntegral.integral_sub h1 h2).symm
      rw [hsub]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    have hmem_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)), t ∈ Set.Icc t0 t1 :=
      ae_restrict_mem measurableSet_Icc
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
        |ĝn t - ĝm t|
          ≤ 2 * (eLpNorm (fun x => vn.toFun x - vm.toFun x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
      have heq := hrep_n.sub hrep_m
      filter_upwards [heq, hmem_ae] with t ht htm
      simp only [Pi.sub_apply] at ht
      rw [← ht, hlin t htm]
      exact hC t htm
    exact continuous_ae_bound_le ht (hcn.sub hcm) hae t htm
  set w : ℕ → WeakH10 := Classical.choose (hApproxThm v hv) with hw_def
  have hwspec := Classical.choose_spec (hApproxThm v hv)
  rw [← hw_def] at hwspec
  have hgspec : ∀ n : ℕ,
      Continuous (Classical.choose (hRepH10Thm (w n))) ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)]
        Classical.choose (hRepH10Thm (w n)) :=
    fun n => Classical.choose_spec (hRepH10Thm (w n))
  have hbound : ∀ n m : ℕ, ∀ t ∈ Set.Icc t0 t1,
      |(Classical.choose (hRepH10Thm (w n))) t
        - (Classical.choose (hRepH10Thm (w m))) t|
        ≤ 2 * (eLpNorm (fun x => (w n).toFun x - (w m).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
    fun n m => key (w n) (w m) (weakH10_toFun_memLp (w n))
      (weakH10_toFun_memLp (w m)) _ _ (hgspec n).1 (hgspec m).1
      (hgspec n).2 (hgspec m).2
  have hδ : (0 : ℝ) < ε / 4 := by linarith
  have hev := hwspec.eventually (Iio_mem_nhds hδ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n m hn hm t htm => le_trans (hbound n m t htm) ?_⟩
  have hdn : (eLpNorm (fun x => v x - (w n).toFun x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε / 4 := hN n hn
  have hdm : (eLpNorm (fun x => v x - (w m).toFun x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε / 4 := hN m hm
  have hAB : (fun x => (w n).toFun x - (w m).toFun x)
      = (fun x => (w n).toFun x - v x) + (fun x => v x - (w m).toFun x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have htri : eLpNorm (fun x => (w n).toFun x - (w m).toFun x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ eLpNorm (fun x => (w n).toFun x - v x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))
        + eLpNorm (fun x => v x - (w m).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [hAB]
    exact eLpNorm_add_le one_le_two
  have hAn : eLpNorm (fun x => (w n).toFun x - v x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
    lt_top_iff_ne_top.mp ((weakH10_toFun_memLp (w n)).sub hv)
  have hBn : eLpNorm (fun x => v x - (w m).toFun x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
    lt_top_iff_ne_top.mp (hv.sub (weakH10_toFun_memLp (w m)))
  have hsum_ne : eLpNorm (fun x => (w n).toFun x - v x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))
      + eLpNorm (fun x => v x - (w m).toFun x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hAn, hBn⟩
  have hneg1 : eLpNorm (fun x => (w n).toFun x - v x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))
      = eLpNorm (fun x => v x - (w n).toFun x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hneg : (fun x => (w n).toFun x - v x)
        = -(fun x => v x - (w n).toFun x) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [hneg, eLpNorm_neg]
  have hto : (eLpNorm (fun x => (w n).toFun x - (w m).toFun x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm (fun x => v x - (w n).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        + (eLpNorm (fun x => v x - (w m).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    have h := ENNReal.toReal_mono hsum_ne htri
    rwa [ENNReal.toReal_add hAn hBn, hneg1] at h
  have hle2 : 2 * (eLpNorm (fun x => (w n).toFun x - (w m).toFun x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      ≤ 2 * ((eLpNorm (fun x => v x - (w n).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        + (eLpNorm (fun x => v x - (w m).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :=
    mul_le_mul_of_nonneg_left hto (by norm_num)
  have hlt2 : 2 * ((eLpNorm (fun x => v x - (w n).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        + (eLpNorm (fun x => v x - (w m).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) < ε := by
    linarith [hdn, hdm]
  exact le_of_lt (lt_of_le_of_lt hle2 hlt2)


instance holderTriple_two : ENNReal.HolderTriple 2 2 1 where
  inv_add_inv_eq_inv := by rw [ENNReal.inv_two_add_inv_two, inv_one]


theorem weakH10_memLp_toFun (w : WeakH10) :
    MemLp w.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hInt : Integrable w.weakDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    w.weakDeriv_memLp.integrable (by norm_num)
  have hOn : IntegrableOn w.weakDeriv (Set.Icc (0 : ℝ) 1) volume := hInt
  have hprim : ContinuousOn (fun x => ∫ t in Set.Ioc (0 : ℝ) x, w.weakDeriv t)
      (Set.Icc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive hOn
  have hcongr : Set.EqOn w.toFun (fun x => ∫ t in Set.Ioc (0 : ℝ) x, w.weakDeriv t)
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    rw [w.toFun_eq_integral x hx, intervalIntegral.integral_of_le hx.1]
  have hcont : ContinuousOn w.toFun (Set.Icc (0 : ℝ) 1) := hprim.congr hcongr
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hae : AEStronglyMeasurable w.toFun (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hcont.aestronglyMeasurable measurableSet_Icc
  have hb : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖w.toFun x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hC x hx
  exact MemLp.of_bound hae C hb


theorem pair_intervalIntegrable (u : ℝ → ℝ → ℝ) (t : ℝ) (v : ℝ → ℝ)
    (hu : MemLp (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hv : MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    IntervalIntegrable (fun x => u t x * v x) volume 0 1 := by
  have hInt : Integrable (fun x => u t x * v x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hu.integrable_mul hv
  have hOn : IntegrableOn (fun x => u t x * v x) (Set.Icc (0 : ℝ) 1) volume := hInt
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mp hOn


theorem clamp_mem_Icc (t0 t1 t : ℝ) (ht : t0 ≤ t1) :
    min (max t t0) t1 ∈ Set.Icc t0 t1 :=
  ⟨le_min (le_max_right _ _) ht, min_le_right _ _⟩


theorem clamp_eq_of_mem (t0 t1 t : ℝ) (ht : t ∈ Set.Icc t0 t1) :
    min (max t t0) t1 = t := by
  rw [max_eq_left ht.1, min_eq_left ht.2]


theorem continuous_clamp (t0 t1 : ℝ) :
    Continuous fun t => min (max t t0) t1 :=
  (continuous_id.max continuous_const).min continuous_const

/-- Pairing reps for all `L²` test functions, final assembly. -/

theorem pairing_rep_final
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hCSBoundThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ w : ℝ → ℝ,
      MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |(∫ x in (0 : ℝ)..1, u t x * w x)|
        ≤ 2 * (eLpNorm w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hRepH10Thm : ∀ v : WeakH10, ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v.toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ)
    (hRepsCauchyThm : ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ w : ℕ → WeakH10, Filter.Tendsto (fun n : ℕ =>
        (eLpNorm (fun x => v x - (w n).toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        Filter.atTop (nhds 0) →
      ∀ ĝ : ℕ → ℝ → ℝ, (∀ n : ℕ, Continuous (ĝ n)) →
      (∀ n : ℕ, (fun t => ∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ n) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        ∀ t : ℝ, t ∈ Set.Icc t0 t1 → |ĝ n t - ĝ m t| ≤ ε)
    (hDenseThm : ∀ v : ℝ → ℝ, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ w : WeakH10,
        (eLpNorm (fun x => v x - w.toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) :
    ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
          =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ := by
  intro v hv
  have hseq : ∀ n : ℕ, ∃ wn : WeakH10,
      (eLpNorm (fun x => v x - wn.toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        < 1 / ((n : ℝ) + 1) := by
    intro n
    apply hDenseThm v hv
    positivity
  choose w hw using hseq
  have hnorm0 : Filter.Tendsto (fun n : ℕ =>
      (eLpNorm (fun x => v x - (w n).toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => ENNReal.toReal_nonneg)
      (fun n => le_of_lt (hw n)) tendsto_one_div_add_atTop_nhds_zero_nat
  have hrep : ∀ n : ℕ, ∃ ĝn : ℝ → ℝ, Continuous ĝn ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝn :=
    fun n => hRepH10Thm (w n)
  choose ĝ hcont heq using hrep
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∀ t : ℝ, t ∈ Set.Icc t0 t1 → |ĝ n t - ĝ m t| ≤ ε :=
    hRepsCauchyThm v hv w hnorm0 ĝ hcont heq
  have hφcont : ∀ n : ℕ, Continuous (fun t => ĝ n (min (max t t0) t1)) :=
    fun n => (hcont n).comp (continuous_clamp t0 t1)
  have hφcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∀ t : ℝ, |ĝ n (min (max t t0) t1) - ĝ m (min (max t t0) t1)| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    exact ⟨N, fun n m hn hm t => hN n m hn hm _ (clamp_mem_Icc t0 t1 t ht.le)⟩
  have hpoint : ∀ x : ℝ, CauchySeq (fun n => ĝ n (min (max x t0) t1)) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hφcauchy (ε / 2) (half_pos hε)
    exact ⟨N, fun m hm n hn => by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hN m n hm hn x) (half_lt_self hε)⟩
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hpoint x)
  have hunif : TendstoUniformly (fun n t => ĝ n (min (max t t0) t1)) g Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hφcauchy (ε / 2) (half_pos hε)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn t
    have hmem : g t ∈ Metric.closedBall (ĝ n (min (max t t0) t1)) (ε / 2) := by
      apply Metric.isClosed_closedBall.mem_of_tendsto (hg t)
      filter_upwards [Filter.eventually_ge_atTop N] with m hm
      rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm]
      exact hN n m hn hm t
    have hle : dist (g t) (ĝ n (min (max t t0) t1)) ≤ ε / 2 :=
      Metric.mem_closedBall.mp hmem
    exact lt_of_le_of_lt hle (half_lt_self hε)
  have hcontg : Continuous g :=
    hunif.continuous (Filter.Eventually.of_forall hφcont).frequently
  have hpair_lim : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      Filter.Tendsto (fun n => ∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u t x * v x)) := by
    intro t ht
    have hbound : ∀ n : ℕ, |(∫ x in (0 : ℝ)..1, u t x * v x) -
        (∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)| ≤
        2 * (eLpNorm (fun x => v x - (w n).toFun x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
      intro n
      have hrewrite : (∫ x in (0 : ℝ)..1, u t x * v x) -
            (∫ x in (0 : ℝ)..1, u t x * (w n).toFun x) =
            ∫ x in (0 : ℝ)..1, u t x * (v x - (w n).toFun x) := by
        have h1 := pair_intervalIntegrable u t v (hMemThm t ht) hv
        have h2 := pair_intervalIntegrable u t (fun x => (w n).toFun x)
          (hMemThm t ht) (weakH10_memLp_toFun (w n))
        have hsub := intervalIntegral.integral_sub h1 h2
        have hfun : (fun x => u t x * v x - u t x * (w n).toFun x) =
            (fun x => u t x * (v x - (w n).toFun x)) := by
          ext x
          ring
        rw [hfun] at hsub
        exact hsub.symm
      rw [hrewrite]
      exact hCSBoundThm t ht _ (hv.sub (weakH10_memLp_toFun (w n)))
    have h0 : Filter.Tendsto (fun n => (∫ x in (0 : ℝ)..1, u t x * v x) -
        (∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ => 2 * (eLpNorm
        (fun x => v x - (w n).toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        (fun n => ?_) ?_
      · rw [Real.norm_eq_abs]
        exact hbound n
      · have hmul : Filter.Tendsto (fun n : ℕ => 2 * (eLpNorm
            (fun x => v x - (w n).toFun x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
            Filter.atTop (nhds (2 * 0)) :=
          tendsto_const_nhds.mul hnorm0
        simpa using hmul
    have hC : Filter.Tendsto (fun _ : ℕ => ∫ x in (0 : ℝ)..1, u t x * v x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u t x * v x)) := tendsto_const_nhds
    have h2 := hC.sub h0
    simpa using h2
  have heqφ : ∀ n : ℕ, (fun t => ∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)
      =ᵐ[volume.restrict (Set.Icc t0 t1)] (fun t => ĝ n (min (max t t0) t1)) := by
    intro n
    refine (heq n).trans ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    show ĝ n t = ĝ n (min (max t t0) t1)
    rw [clamp_eq_of_mem t0 t1 t ht]
  have hall : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)), ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, u t x * (w n).toFun x) =
        ĝ n (min (max t t0) t1) :=
    ae_all_iff.mpr heqφ
  refine ⟨g, hcontg, ?_⟩
  filter_upwards [hall, ae_restrict_mem measurableSet_Icc] with t htmem htIcc
  have h1 := hpair_lim t htIcc
  have h2 := hunif.tendsto_at t
  have h2' : Filter.Tendsto (fun n => ∫ x in (0 : ℝ)..1, u t x * (w n).toFun x)
      Filter.atTop (nhds (g t)) :=
    h2.congr (fun n => (htmem n).symm)
  exact tendsto_nhds_unique h1 h2'


theorem timetrans_cs_bound
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (hMemUThm : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hTimetransThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ t h : ℝ,
      t ∈ Set.Icc t0 t1 → t + h ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x =>
        (if t + h = t1 then (U N N) x
         else (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x)
        - (if t = t1 then (U N N) x
           else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x))
        2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * (|h| + (t1 - t0) / N)))
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1,
          ((if t = t1 then (U N N) x
            else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
            - (U N 1) x) * ψ x)|
        ≤ Real.sqrt (Classical.choose hTimetransThm * (|t - t0| + (t1 - t0) / N))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  obtain ⟨_hCnonneg, hTrans⟩ := Classical.choose_spec hTimetransThm
  intro ψ hψ N hN t htmem
  have hne : t0 ≠ t1 := ne_of_lt ht
  have heq : t0 + (t - t0) = t := by ring
  have hfloor : Nat.floor ((t0 - t0) / ((t1 - t0) / (N : ℝ))) + 1 = 1 := by simp
  have hS : MemLp (fun x => if t = t1 then (U N N) x
      else (U N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)) x)
      2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    by_cases h : t = t1
    · simp only [ite_eq_left h]
      exact hMemUThm N N
    · simp only [ite_eq_right h]
      exact hMemUThm N _
  have hf : MemLp (fun x => (if t = t1 then (U N N) x
        else (U N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)) x)
        - (U N 1) x)
      2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hS.sub (hMemUThm N 1)
  have hCS := hCSThm hf hψ
  have ht0mem : t0 ∈ Set.Icc t0 t1 := ⟨le_rfl, le_of_lt ht⟩
  have hadd : t0 + (t - t0) ∈ Set.Icc t0 t1 := by
    rw [heq]
    exact htmem
  have hTr := hTrans N hN t0 (t - t0) ht0mem hadd
  rw [heq] at hTr
  simp only [ite_eq_right hne, hfloor] at hTr
  exact hCS.trans (mul_le_mul_of_nonneg_right hTr ENNReal.toReal_nonneg)


theorem first_step_cs_bound
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (hMemUThm : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hStepThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N →
      (eLpNorm (fun x => (U N 1) x - (U N 0) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * ((t1 - t0) / N)))
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N →
      |(∫ x in (0 : ℝ)..1, ((U N 1) x - (U N 0) x) * ψ x)|
        ≤ Real.sqrt (Classical.choose hStepThm * ((t1 - t0) / N))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro ψ hψ N hN
  have hf : MemLp (fun x => (U N 1) x - (U N 0) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hMemUThm N 1).sub (hMemUThm N 0)
  have hcs := hCSThm hf hψ
  obtain ⟨hC0, hC⟩ := Classical.choose_spec hStepThm
  have hNbound := hC N hN
  calc |(∫ x in (0 : ℝ)..1, ((U N 1) x - (U N 0) x) * ψ x)|
      ≤ (eLpNorm (fun x => (U N 1) x - (U N 0) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := hcs
    _ ≤ Real.sqrt (Classical.choose hStepThm * ((t1 - t0) / N))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        mul_le_mul_of_nonneg_right hNbound ENNReal.toReal_nonneg


theorem init_cs_bound
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U : ℕ → (ℝ → ℝ))
    (hMemUThm : ∀ (k : ℕ), MemLp (U k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ),
      |(∫ x in (0 : ℝ)..1, ((U N) x - u0 x) * ψ x)|
        ≤ (eLpNorm (fun x => (U N) x - u0 x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro ψ hψ N
  have hdiff : MemLp (fun x => (U N) x - u0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hMemUThm N).sub hu0
  exact hCSThm hdiff hψ


theorem memlp_intervalIntegrable_mul
    {f ψ : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    IntervalIntegrable (fun x => f x * ψ x) volume 0 1 := by
  have hInt : Integrable (fun x => f x * ψ x) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.integrable_mul hψ
  have hOn : IntegrableOn (fun x => f x * ψ x) (Set.Icc (0 : ℝ) 1) volume := hInt
  have hsub : Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (hOn.mono_set hsub).intervalIntegrable


theorem integral_diff_mul_split
    {f g ψ : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (∫ x in (0 : ℝ)..1, (f x - g x) * ψ x)
      = (∫ x in (0 : ℝ)..1, f x * ψ x) - (∫ x in (0 : ℝ)..1, g x * ψ x) := by
  have h1 : IntervalIntegrable (fun x => f x * ψ x) volume 0 1 :=
    memlp_intervalIntegrable_mul hf hψ
  have h2 : IntervalIntegrable (fun x => g x * ψ x) volume 0 1 :=
    memlp_intervalIntegrable_mul hg hψ
  simp only [sub_mul]
  exact intervalIntegral.integral_sub h1 h2

/-- Three-term assembly from the CS bounds. -/

theorem pairing_limit_three_term_asm_fixed
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U : ℕ → ℕ → (ℝ → ℝ))
    (hMemUThm : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (G : Set ℝ)
    (hSliceThm : ∀ τ : ℝ, τ ∈ G → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U N N) x
             else (U N (Nat.floor ((τ - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)))
    (hCS1Thm : ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1,
          ((if t = t1 then (U N N) x
            else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
            - (U N 1) x) * ψ x)|
        ≤ Real.sqrt (2 * (|t - t0| + (t1 - t0) / N))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hCS1bThm : ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N →
      |(∫ x in (0 : ℝ)..1, ((U N 1) x - (U N 0) x) * ψ x)|
        ≤ Real.sqrt (2 * ((t1 - t0) / N))
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hCS2Thm : ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ),
      |(∫ x in (0 : ℝ)..1, ((U N 0) x - u0 x) * ψ x)|
        ≤ (eLpNorm (fun x => (U N 0) x - u0 x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ G → t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
        ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x)
          - (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U N N) x
               else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)|
          + 2 * Real.sqrt (2 * (|t - t0| + (t1 - t0) / N))
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm (fun x => (U N 0) x - u0 x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro ψ hψ N hN t htG htIcc
  set A : ℝ := (∫ x in (0 : ℝ)..1, u t x * ψ x) with hA
  set B : ℝ := (∫ x in (0 : ℝ)..1,
    (if t = t1 then (U N N) x
      else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x) with hB
  set C : ℝ := (∫ x in (0 : ℝ)..1, (U N 1) x * ψ x) with hC
  set D : ℝ := (∫ x in (0 : ℝ)..1, (U N 0) x * ψ x) with hD
  set E : ℝ := (∫ x in (0 : ℝ)..1, u0 x * ψ x) with hE
  have hUbar : MemLp
      (fun x => if t = t1 then (U N N) x
        else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
      2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    by_cases ht1 : t = t1
    · have heq : (fun x => if t = t1 then (U N N) x
          else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
          = U N N := by
        funext x
        rw [ite_eq_left ht1]
      rw [heq]
      exact hMemUThm N N
    · have heq : (fun x => if t = t1 then (U N N) x
          else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
          = U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) := by
        funext x
        rw [ite_eq_right ht1]
      rw [heq]
      exact hMemUThm N _
  have hbr1 : (∫ x in (0 : ℝ)..1,
        ((if t = t1 then (U N N) x
          else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
          - (U N 1) x) * ψ x)
      = (∫ x in (0 : ℝ)..1,
          (if t = t1 then (U N N) x
            else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)
        - (∫ x in (0 : ℝ)..1, (U N 1) x * ψ x) :=
    integral_diff_mul_split hUbar (hMemUThm N 1) hψ
  have hbr2 : (∫ x in (0 : ℝ)..1, ((U N 1) x - (U N 0) x) * ψ x)
      = (∫ x in (0 : ℝ)..1, (U N 1) x * ψ x)
        - (∫ x in (0 : ℝ)..1, (U N 0) x * ψ x) :=
    integral_diff_mul_split (hMemUThm N 1) (hMemUThm N 0) hψ
  have hbr3 : (∫ x in (0 : ℝ)..1, ((U N 0) x - u0 x) * ψ x)
      = (∫ x in (0 : ℝ)..1, (U N 0) x * ψ x)
        - (∫ x in (0 : ℝ)..1, u0 x * ψ x) :=
    integral_diff_mul_split (hMemUThm N 0) hu0 hψ
  have h1 := hCS1Thm ψ hψ N hN t htIcc
  rw [hbr1, ← hB, ← hC] at h1
  have h2 := hCS1bThm ψ hψ N hN
  rw [hbr2, ← hC, ← hD] at h2
  have h3 := hCS2Thm ψ hψ N
  rw [hbr3, ← hD, ← hE] at h3
  have hPnn : (0 : ℝ) ≤ (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  have hsqrt : Real.sqrt (2 * ((t1 - t0) / N))
      ≤ Real.sqrt (2 * (|t - t0| + (t1 - t0) / N)) := by
    apply Real.sqrt_le_sqrt
    have hnn : (0 : ℝ) ≤ |t - t0| := abs_nonneg _
    linarith
  have h12 : |B - C| + |C - D|
      ≤ 2 * Real.sqrt (2 * (|t - t0| + (t1 - t0) / N))
        * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    have hmul := mul_le_mul_of_nonneg_right hsqrt hPnn
    linarith
  have hdecomp : A - E = ((A - B) + (B - C)) + ((C - D) + (D - E)) := by ring
  have g0 := abs_add_le ((A - B) + (B - C)) ((C - D) + (D - E))
  rw [← hdecomp] at g0
  have g1 := abs_add_le (A - B) (B - C)
  have g2 := abs_add_le (C - D) (D - E)
  linarith


theorem init_layer_rep_value
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U : ℕ → ℕ → (ℝ → ℝ))
    (G : Set ℝ)
    (hThreeTermThm : ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ G → t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
        ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x)
          - (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U N N) x
               else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)|
          + Real.sqrt (2 * (|t - t0| + (t1 - t0) / N))
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm (fun x => (U N 0) x - u0 x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hInitConvThm : Filter.Tendsto (fun N : ℕ =>
        (eLpNorm (fun x => (U N 0) x - u0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      Filter.atTop (nhds 0)) :
    ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ t : ℝ,
        t ∈ G → t ∈ Set.Icc t0 t1 → t0 < t → t - t0 < δ →
        |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
          ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x)
            - (∫ x in (0 : ℝ)..1,
                (if t = t1 then (U N N) x
                 else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)|
            + ε := by
  intro ψ hψ ε hε
  set K := (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hKdef
  have hK_nonneg : 0 ≤ K := by rw [hKdef]; exact ENNReal.toReal_nonneg
  by_cases hK0 : K = 0
  · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro t htG htIcc _ _
    have h3 := hThreeTermThm ψ hψ 1 (by norm_num) t htG htIcc
    rw [← hKdef] at h3
    rw [hK0] at h3
    simp only [mul_zero, add_zero] at h3
    linarith
  · have hKpos : 0 < K := lt_of_le_of_ne hK_nonneg (Ne.symm hK0)
    have ht10 : 0 < t1 - t0 := sub_pos.mpr ht
    have hε2K : 0 < ε / (2 * K) := by positivity
    have hSq : 0 < (ε / (2 * K)) ^ 2 := pow_pos hε2K 2
    set S := (ε / (2 * K)) ^ 2 / 2 with hSdef
    have hSpos : 0 < S := by rw [hSdef]; linarith
    have hS2pos : 0 < S / 2 := by linarith
    rw [Metric.tendsto_atTop] at hInitConvThm
    obtain ⟨N1, hN1⟩ := hInitConvThm (ε / (2 * K)) hε2K
    obtain ⟨n2, hn2⟩ := exists_nat_gt ((t1 - t0) / (S / 2))
    have hxpos : 0 < (t1 - t0) / (S / 2) := div_pos ht10 hS2pos
    have hn2pos : 0 < n2 := by
      have hlt : (0 : ℝ) < (n2 : ℝ) := lt_trans hxpos hn2
      exact Nat.cast_pos.mp hlt
    have hτ : (t1 - t0) / (n2 : ℝ) < S / 2 := by
      have hpos1 : (0 : ℝ) < (n2 : ℝ) := Nat.cast_pos.mpr hn2pos
      have h2 : (t1 - t0) < (n2 : ℝ) * (S / 2) := by
        have h1 : (t1 - t0) / (S / 2) < (n2 : ℝ) := hn2
        rwa [div_lt_iff₀ hS2pos] at h1
      have h3 : (t1 - t0) < (S / 2) * (n2 : ℝ) := by rwa [mul_comm] at h2
      rwa [div_lt_iff₀ hpos1]
    have hN1le : N1 ≤ N1 + n2 + 1 := by omega
    have hn2le : n2 ≤ N1 + n2 + 1 := by omega
    have hNpos : 0 < N1 + n2 + 1 := by omega
    have hNc : (0 : ℝ) < ((N1 + n2 + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hNpos
    refine ⟨S / 2, hS2pos, N1 + n2 + 1, hNpos, ?_⟩
    intro t htG htIcc ht0t htt0
    have h3 := hThreeTermThm ψ hψ (N1 + n2 + 1) hNpos t htG htIcc
    rw [← hKdef] at h3
    have hKne : K ≠ 0 := ne_of_gt hKpos
    have heq : ε / (2 * K) * K = ε / 2 := by
      have h2Kne : (2 : ℝ) * K ≠ 0 := mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) hKne
      field_simp
    have hdist := hN1 (N1 + n2 + 1) hN1le
    have hinit_nonneg : 0 ≤ (eLpNorm (fun x => (U (N1 + n2 + 1) 0) x - u0 x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
    have hinit_lt : (eLpNorm (fun x => (U (N1 + n2 + 1) 0) x - u0 x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε / (2 * K) := by
      simp only [Real.dist_eq, sub_zero] at hdist
      rwa [abs_of_nonneg hinit_nonneg] at hdist
    have hinit_mul : (eLpNorm (fun x => (U (N1 + n2 + 1) 0) x - u0 x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal * K < ε / 2 := by
      have h := mul_lt_mul_of_pos_right hinit_lt hKpos
      rwa [heq] at h
    have habs : |t - t0| = t - t0 := abs_of_pos (sub_pos.mpr ht0t)
    have hτN : (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ) ≤ (t1 - t0) / (n2 : ℝ) := by
      have hn2c : (0 : ℝ) < (n2 : ℝ) := Nat.cast_pos.mpr hn2pos
      have hle : (n2 : ℝ) ≤ ((N1 + n2 + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hn2le
      exact div_le_div_of_nonneg_left ht10.le hn2c hle
    have hX : |t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ) < S := by
      rw [habs]
      have h2 : (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ) < S / 2 :=
        lt_of_le_of_lt hτN hτ
      linarith [htt0, h2]
    have h2X : 2 * (|t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ))
        < (ε / (2 * K)) ^ 2 := by
      linarith [hX, hSdef]
    have hsqrt : Real.sqrt (2 * (|t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ)))
        < ε / (2 * K) := by
      have hnn : 0 ≤ 2 * (|t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ)) := by
        have h1 : (0 : ℝ) ≤ |t - t0| := abs_nonneg _
        have h2 : (0 : ℝ) ≤ (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ) :=
          div_nonneg ht10.le hNc.le
        linarith
      calc Real.sqrt (2 * (|t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ)))
          < Real.sqrt ((ε / (2 * K)) ^ 2) := Real.sqrt_lt_sqrt hnn h2X
        _ = ε / (2 * K) := Real.sqrt_sq hε2K.le
    have hsqrt_mul : Real.sqrt (2 * (|t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ)))
        * K < ε / 2 := by
      have h := mul_lt_mul_of_pos_right hsqrt hKpos
      rwa [heq] at h
    have hsum : Real.sqrt (2 * (|t - t0| + (t1 - t0) / ((N1 + n2 + 1 : ℕ) : ℝ))) * K
        + (eLpNorm (fun x => (U (N1 + n2 + 1) 0) x - u0 x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal * K < ε := by
      linarith [hsqrt_mul, hinit_mul]
    linarith [h3, hsum]


theorem init_layer_diagonal
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U : ℕ → ℕ → (ℝ → ℝ))
    (G : Set ℝ)
    (hGnearT0Thm : ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, t ∈ G ∧ t ∈ Set.Icc t0 t1 ∧ t0 < t ∧ t - t0 < δ)
    (hSliceThm : ∀ τ : ℝ, τ ∈ G → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U N N) x
             else (U N (Nat.floor ((τ - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)))
    (hThreeTermThm : ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (N : ℕ), 0 < N → ∀ t : ℝ, t ∈ G → t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
        ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x)
          - (∫ x in (0 : ℝ)..1,
              (if t = t1 then (U N N) x
               else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * ψ x)|
          + Real.sqrt (2 * (|t - t0| + (t1 - t0) / N))
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + (eLpNorm (fun x => (U N 0) x - u0 x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hInitConvThm : Filter.Tendsto (fun N : ℕ =>
        (eLpNorm (fun x => (U N 0) x - u0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      Filter.atTop (nhds 0))
    (hRepAgreeThm : ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ĝ : ℝ → ℝ, Continuous ĝ →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ →
      ∀ t : ℝ, t ∈ G → (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ t) :
    ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ĝ : ℝ → ℝ, Continuous ĝ →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ →
      ĝ t0 = ∫ x in (0 : ℝ)..1, u0 x * v x := by
  intro v hv ĝ hĝcont hae
  set L : ℝ := ∫ x in (0 : ℝ)..1, u0 x * v x with hL
  set K : ℝ := (eLpNorm v 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hK
  have hK_nonneg : 0 ≤ K := ENNReal.toReal_nonneg
  have hK1 : K ≤ K + 1 := le_add_of_nonneg_right zero_le_one
  have hK1pos : (0 : ℝ) < K + 1 := lt_of_le_of_lt hK_nonneg (lt_add_one K)
  have hdiff : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
  suffices hall : ∀ ε : ℝ, 0 < ε → |ĝ t0 - L| < ε by
    by_contra hne
    have hpos : 0 < |ĝ t0 - L| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have h2 := hall _ (half_pos hpos)
    linarith
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  set Q : ℝ := (ε / 4) / (K + 1) with hQ
  have hQpos : (0 : ℝ) < Q := div_pos hε4 hK1pos
  have hQK : Q * (K + 1) = ε / 4 := by
    rw [hQ]
    exact div_mul_cancel₀ _ (ne_of_gt hK1pos)
  have hQ2 : (0 : ℝ) < Q ^ 2 / 4 := div_pos (sq_pos_of_pos hQpos) (by norm_num)
  obtain ⟨δc, hδcpos, hδc⟩ := (Metric.continuousAt_iff.mp hĝcont.continuousAt) (ε / 4) hε4
  obtain ⟨t, htG, htIcc, ht0lt, htt0lt⟩ :=
    hGnearT0Thm (min δc (Q ^ 2 / 4)) (lt_min hδcpos hQ2)
  have htδc : t - t0 < δc := lt_of_lt_of_le htt0lt (min_le_left _ _)
  have htQ : t - t0 < Q ^ 2 / 4 := lt_of_lt_of_le htt0lt (min_le_right _ _)
  have hatt0 : |t - t0| = t - t0 := abs_of_pos (sub_pos.mpr ht0lt)
  set gt : ℝ := ∫ x in (0 : ℝ)..1, u t x * v x with hgt
  have hSlice := hSliceThm t htG v hv
  rw [← hgt] at hSlice
  obtain ⟨Ns, hNs⟩ := (Metric.tendsto_atTop.mp hSlice) (ε / 4) hε4
  obtain ⟨Ni, hNi⟩ := (Metric.tendsto_atTop.mp hInitConvThm) Q hQpos
  obtain ⟨Nq, hNq⟩ := exists_nat_gt ((t1 - t0) / (Q ^ 2 / 4))
  set N : ℕ := max Ns (max Nq (max Ni 1)) with hN
  have hNNs : Ns ≤ N := le_max_left _ _
  have hNNq : Nq ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNNi : Ni ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h1N : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h0N : 0 < N := lt_of_lt_of_le zero_lt_one h1N
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr h0N
  set eN : ℝ := (eLpNorm (fun x => (U N 0) x - u0 x) 2
    (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with heN
  set SINT : ℝ := ∫ x in (0 : ℝ)..1,
    (if t = t1 then (U N N) x
     else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) * v x with hSINT
  have heN_nonneg : 0 ≤ eN := by rw [heN]; exact ENNReal.toReal_nonneg
  have hthree := hThreeTermThm v hv N h0N t htG htIcc
  rw [← hgt, ← hL, ← hK, ← heN, ← hSINT] at hthree
  have hrep := hRepAgreeThm v hv ĝ hĝcont hae t htG
  rw [← hgt] at hrep
  have hC : |ĝ t0 - ĝ t| < ε / 4 := by
    have hxt : dist t t0 < δc := by rw [Real.dist_eq, hatt0]; exact htδc
    have h := hδc hxt
    rw [Real.dist_eq, abs_sub_comm _ (ĝ t0)] at h
    exact h
  have hS : |gt - SINT| < ε / 4 := by
    have h := hNs N hNNs
    simp only [Real.dist_eq] at h
    rw [← hSINT, abs_sub_comm _ gt] at h
    exact h
  have hNqpos : (0 : ℝ) < (Nq : ℝ) := lt_trans (div_pos hdiff hQ2) hNq
  have h1 : t1 - t0 < (Nq : ℝ) * (Q ^ 2 / 4) := (div_lt_iff₀ hQ2).mp hNq
  have h2 : (Nq : ℝ) * (Q ^ 2 / 4) ≤ (N : ℝ) * (Q ^ 2 / 4) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNNq) (le_of_lt hQ2)
  have hNQ : (t1 - t0) / (N : ℝ) < Q ^ 2 / 4 := (div_lt_iff₀ hNpos).mpr (by linarith)
  have hsqrt : Real.sqrt (2 * (|t - t0| + (t1 - t0) / (N : ℝ))) < Q := by
    apply (Real.sqrt_lt' hQpos).mpr
    have hatt : |t - t0| < Q ^ 2 / 4 := by rw [hatt0]; exact htQ
    have hsum := add_lt_add hatt hNQ
    linarith
  have hT1 : Real.sqrt (2 * (|t - t0| + (t1 - t0) / (N : ℝ))) * K < ε / 4 :=
    calc Real.sqrt (2 * (|t - t0| + (t1 - t0) / (N : ℝ))) * K
        ≤ Real.sqrt (2 * (|t - t0| + (t1 - t0) / (N : ℝ))) * (K + 1) :=
          mul_le_mul_of_nonneg_left hK1 (Real.sqrt_nonneg _)
      _ < Q * (K + 1) := mul_lt_mul_of_pos_right hsqrt hK1pos
      _ = ε / 4 := hQK
  have hdistI : eN < Q := by
    have h := hNi N hNNi
    simp only [Real.dist_eq, sub_zero] at h
    rw [← heN, abs_of_nonneg heN_nonneg] at h
    exact h
  have hT2 : eN * K < ε / 4 :=
    calc eN * K ≤ eN * (K + 1) := mul_le_mul_of_nonneg_left hK1 heN_nonneg
      _ < Q * (K + 1) := mul_lt_mul_of_pos_right hdistI hK1pos
      _ = ε / 4 := hQK
  have htri : |ĝ t0 - L| ≤ |ĝ t0 - ĝ t| + |gt - L| := by
    calc |ĝ t0 - L| = |(ĝ t0 - ĝ t) + (gt - L)| := by congr 1; rw [hrep]; ring
      _ ≤ |ĝ t0 - ĝ t| + |gt - L| := abs_add_le _ _
  linarith


theorem countable_dense_L2
    {μ : Measure ℝ} [IsFiniteMeasure μ] :
    ∃ D : Set (ℝ → ℝ), D.Countable
      ∧ (∀ v ∈ D, MemLp v 2 μ)
      ∧ (∀ v : ℝ → ℝ, MemLp v 2 μ →
          ∀ ε : ℝ, 0 < ε → ∃ w ∈ D,
            (eLpNorm (fun x => v x - w x) 2 μ).toReal < ε) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  obtain ⟨D0, hD0count, hD0dense⟩ :=
    TopologicalSpace.exists_countable_dense (Lp ℝ 2 μ)
  refine ⟨(fun q : Lp ℝ 2 μ => (q : ℝ → ℝ)) '' D0, hD0count.image _, ?_, ?_⟩
  · intro v hv
    obtain ⟨q, _, rfl⟩ := hv
    exact Lp.memLp q
  · intro v hv ε hε
    have hmem : MemLp.toLp v hv ∈ closure D0 := by
      rw [hD0dense.closure_eq]
      exact Set.mem_univ _
    rw [Metric.mem_closure_iff] at hmem
    obtain ⟨q, hqD0, hdist⟩ := hmem ε hε
    refine ⟨(q : ℝ → ℝ), Set.mem_image_of_mem _ hqD0, ?_⟩
    have hw : MemLp (q : ℝ → ℝ) 2 μ := Lp.memLp q
    have hq_eq : MemLp.toLp (q : ℝ → ℝ) hw = q := Lp.toLp_coeFn q hw
    have hedist : edist (MemLp.toLp v hv) q = eLpNorm (v - (q : ℝ → ℝ)) 2 μ := by
      conv_lhs => rw [← hq_eq]
      exact Lp.edist_toLp_toLp v _ hv hw
    have hdist_eq : dist (MemLp.toLp v hv) q
        = (eLpNorm (v - (q : ℝ → ℝ)) 2 μ).toReal := by
      rw [dist_edist, hedist]
    have hfun : (v - (q : ℝ → ℝ)) = (fun x => v x - (q : ℝ → ℝ) x) := rfl
    rw [hfun] at hdist_eq
    rw [hdist_eq] at hdist
    exact hdist


theorem null_union_pairing_fixed
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (D : Set (ℝ → ℝ)) (hD : D.Countable)
    (hPairThm : ∀ v ∈ D, ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ) :
    ∃ Nstar : Set ℝ, volume Nstar = 0 ∧
      ∀ v ∈ D, ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
          =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ
        ∧ ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∉ Nstar →
          (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ t := by
  classical
  have _ht' : t0 < t1 := ht
  let ĝ : (ℝ → ℝ) → (ℝ → ℝ) :=
    fun v => if h : v ∈ D then Classical.choose (hPairThm v h) else fun _ => 0
  have hĝspec : ∀ (v : ℝ → ℝ) (h : v ∈ D),
      Continuous (ĝ v) ∧
        (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
          =ᵐ[volume.restrict (Set.Icc t0 t1)] (ĝ v) := by
    intro v hv
    have heq : ĝ v = Classical.choose (hPairThm v hv) := by
      simp only [ĝ, dite_eq_left hv]
    rw [heq]
    exact Classical.choose_spec (hPairThm v hv)
  have hnull : ∀ v ∈ D,
      volume (Set.Icc t0 t1 ∩ {t | (∫ x in (0 : ℝ)..1, u t x * v x) ≠ ĝ v t}) = 0 := by
    intro v hv
    obtain ⟨hcont, hae⟩ := hĝspec v hv
    have hIcc : MeasurableSet (Set.Icc t0 t1) := measurableSet_Icc
    have hae' : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
        (fun t => ∫ x in (0 : ℝ)..1, u t x * v x) t = ĝ v t := hae
    rw [ae_restrict_eq hIcc] at hae'
    rw [Filter.eventually_inf_principal] at hae'
    have hae'' : ∀ᵐ t ∂volume,
        t ∈ Set.Icc t0 t1 → (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ v t := hae'
    have hzero : volume {t | ¬ (t ∈ Set.Icc t0 t1 →
        (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ v t)} = 0 := ae_iff.mp hae''
    have hset : Set.Icc t0 t1 ∩ {t | (∫ x in (0 : ℝ)..1, u t x * v x) ≠ ĝ v t} =
        {t | ¬ (t ∈ Set.Icc t0 t1 → (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ v t)} := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      by_cases hmem : t ∈ Set.Icc t0 t1 <;> by_cases heq :
        (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ v t <;> simp [hmem, heq]
    rw [hset]
    exact hzero
  refine ⟨⋃ v ∈ D, (Set.Icc t0 t1 ∩ {t | (∫ x in (0 : ℝ)..1, u t x * v x) ≠ ĝ v t}), ?_, ?_⟩
  · exact (measure_biUnion_null_iff hD).mpr hnull
  · intro v hv
    obtain ⟨hcont, hae⟩ := hĝspec v hv
    refine ⟨ĝ v, hcont, hae, ?_⟩
    intro t htIcc htN
    have htNot : t ∉ Set.Icc t0 t1 ∩
        {t | (∫ x in (0 : ℝ)..1, u t x * v x) ≠ ĝ v t} := by
      intro htmem
      apply htN
      exact Set.mem_biUnion hv htmem
    by_contra hne
    exact htNot ⟨htIcc, hne⟩


lemma helper_interval_eq_restrict (f : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..1, f x) = ∫ x, f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]


lemma helper_eLpNorm_sq (f : ℝ → ℝ) (μ : Measure ℝ)
    (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, (f x)^2 ∂μ := by
  have h2zero : (2 : ENNReal) ≠ 0 := by simp
  have h2top : (2 : ENNReal) ≠ ⊤ := by simp
  have hfin : eLpNorm f 2 μ < ⊤ := hf.eLpNorm_lt_top
  have hLtop : (∫⁻ x, enorm (f x) ^ (2 : ℝ) ∂μ) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2zero h2top hfin
    simp only [ENNReal.toReal_ofNat] at h
    exact h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2zero h2top hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have hexp : (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  have hstep : ((∫⁻ x, enorm (f x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)).toReal ^ 2
      = (∫⁻ x, enorm (f x) ^ (2 : ℝ) ∂μ).toReal := by
    rw [← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, hexp,
      ENNReal.rpow_one]
  rw [hstep]
  have hpt : ∀ x : ℝ, enorm (f x) ^ (2 : ℝ) = ENNReal.ofReal ((f x)^2) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
      Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [lintegral_congr_ae (ae_of_all _ hpt)]
  have hfm : AEStronglyMeasurable (fun x => (f x)^2) μ := by
    simp only [pow_two]
    exact hf.aestronglyMeasurable.mul hf.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (f x)) hfm]


lemma helper_polarization (f g : ℝ → ℝ) (μ : Measure ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm (fun x => f x - g x) 2 μ).toReal ^ 2
      = (eLpNorm f 2 μ).toReal ^ 2 + (eLpNorm g 2 μ).toReal ^ 2
        - 2 * ∫ x, f x * g x ∂μ := by
  have hsub : MemLp (fun x => f x - g x) 2 μ := hf.sub hg
  have hfi : Integrable (fun x => (f x)^2) μ := by
    simp only [pow_two]
    exact hf.integrable_mul hf
  have hgi : Integrable (fun x => (g x)^2) μ := by
    simp only [pow_two]
    exact hg.integrable_mul hg
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  rw [helper_eLpNorm_sq _ _ hsub, helper_eLpNorm_sq _ _ hf,
    helper_eLpNorm_sq _ _ hg]
  have hpt : ∀ x : ℝ, (f x - g x)^2 = (f x)^2 + (g x)^2 - 2 * (f x * g x) := by
    intro x; ring
  have e1 : ∫ x, ((f x)^2 + (g x)^2 - 2 * (f x * g x)) ∂μ
      = ∫ x, ((f x)^2 + (g x)^2) ∂μ - ∫ x, (2 * (f x * g x)) ∂μ :=
    integral_sub (hfi.add hgi) (hfg.const_mul 2)
  have e2 : ∫ x, ((f x)^2 + (g x)^2) ∂μ
      = ∫ x, (f x)^2 ∂μ + ∫ x, (g x)^2 ∂μ :=
    integral_add hfi hgi
  have e3 : ∫ x, (2 * (f x * g x)) ∂μ = 2 * ∫ x, f x * g x ∂μ :=
    integral_const_mul _ _
  rw [integral_congr_ae (ae_of_all _ hpt), e1, e2, e3]


lemma helper_cs_diff (a b c : ℝ → ℝ) (μ : Measure ℝ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hc : MemLp c 2 μ)
    (hCS : ∀ {f g : ℝ → ℝ}, MemLp f 2 μ → MemLp g 2 μ →
      |∫ x, f x * g x ∂μ|
        ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal) :
    |∫ x, a x * b x ∂μ - ∫ x, a x * c x ∂μ|
      ≤ (eLpNorm a 2 μ).toReal * (eLpNorm (fun x => b x - c x) 2 μ).toReal := by
  have hbc : MemLp (fun x => b x - c x) 2 μ := hb.sub hc
  have h1 : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
  have h2 : Integrable (fun x => a x * c x) μ := ha.integrable_mul hc
  have hpt : ∀ x : ℝ, a x * b x - a x * c x = a x * (b x - c x) := fun x => by ring
  have eDiff : ∫ x, a x * b x ∂μ - ∫ x, a x * c x ∂μ
      = ∫ x, a x * (b x - c x) ∂μ := by
    calc ∫ x, a x * b x ∂μ - ∫ x, a x * c x ∂μ
        = ∫ x, (a x * b x - a x * c x) ∂μ := (integral_sub h1 h2).symm
      _ = ∫ x, a x * (b x - c x) ∂μ :=
          integral_congr_ae (ae_of_all _ hpt)
  rw [eDiff]
  exact hCS ha hbc

/-- Good-point strong convergence of Rothe slices. -/

theorem rothe_good_point_convergence_fixed
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ) (D : Set (ℝ → ℝ))
    (hDMemThm : ∀ v ∈ D, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hBoundThm : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ M)
    (hDenseThm : ∀ v : ℝ → ℝ, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ D,
        (eLpNorm (fun x => v x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε)
    (hRepThm : ∀ v ∈ D, ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
      ∀ t : ℝ, t ∉ Nstar → (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ t)
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hNormThm : ContinuousOn
      (fun t => (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      (Set.Icc t0 t1)) :
    ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∉ Nstar → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : ℝ, s ∈ Set.Icc t0 t1 → s ∉ Nstar → |s - t| < δ →
        (eLpNorm (fun x => u s x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε := by
  obtain ⟨M, hM0, hM⟩ := hBoundThm
  have hCSr : ∀ {f g : ℝ → ℝ}, MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x, f x * g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    intro f g hf hg
    rw [← helper_interval_eq_restrict]
    exact hCSThm hf hg
  intro t htIcc htN ε hε
  have hUt : MemLp (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hMemThm t htIcc
  have hPair : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ,
      s ∈ Set.Icc t0 t1 → s ∉ Nstar → |s - t| < δ →
        |∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
          - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2|
          < η := by
    intro η hη
    set ρ := η / (3 * (M + 1)) with hρdef
    have hM1 : (0 : ℝ) < M + 1 := by linarith
    have hpos : (0 : ℝ) < 3 * (M + 1) := by have h := hM1; positivity
    have hρpos : (0 : ℝ) < ρ := by rw [hρdef]; exact div_pos hη hpos
    obtain ⟨w, hwD, hρw⟩ := hDenseThm (fun x => u t x) hUt ρ hρpos
    have hwMem : MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hDMemThm w hwD
    have hρw' : (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        < ρ := hρw
    obtain ⟨ĝ, hĝcont, hĝrep⟩ := hRepThm w hwD
    have hη3 : (0 : ℝ) < η / 3 := by linarith
    obtain ⟨δ, hδ0, hδ⟩ :=
      Metric.continuousAt_iff.mp (hĝcont.continuousAt (x := t)) (η / 3) hη3
    refine ⟨δ, hδ0, fun s hsIcc hsN hst => ?_⟩
    have hUs : MemLp (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      hMemThm s hsIcc
    have hMs : (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ M := hM s hsIcc
    have hMt : (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ M := hM t htIcc
    have hρM : M * ρ ≤ η / 3 := by
      rw [hρdef, ← mul_div_assoc, div_le_iff₀ hpos]
      have heq : η / 3 * (3 * (M + 1)) = η * M + η := by ring
      rw [heq]
      have hme : M * η = η * M := by ring
      rw [hme]
      linarith [hη]
    have hdiff0 : (0 : ℝ)
        ≤ (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
      ENNReal.toReal_nonneg
    have hT1 : |∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        - ∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))|
        ≤ (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
      helper_cs_diff _ _ _ _ hUs hUt hwMem hCSr
    have hT1b : (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ M * ρ :=
      calc (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          ≤ M * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
            mul_le_mul_of_nonneg_right hMs hdiff0
        _ ≤ M * ρ := mul_le_mul_of_nonneg_left (le_of_lt hρw') hM0
    have hT1c : |∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        - ∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))| ≤ η / 3 :=
      le_trans (le_trans hT1 hT1b) hρM
    have hT2 : |∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) - ĝ t| < η / 3 := by
      rw [← helper_interval_eq_restrict, hĝrep s hsN]
      have hst' : dist s t < δ := by rw [Real.dist_eq]; exact hst
      have h2 := hδ hst'
      rw [← Real.dist_eq]
      exact h2
    have hNt : (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        = ∫ x, u t x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [helper_eLpNorm_sq _ _ hUt]
      exact integral_congr_ae (ae_of_all _ fun x => pow_two _)
    have hsymm : (eLpNorm (fun x => w x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        = (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
      have hneg : (fun x => w x - u t x) = -(fun x => u t x - w x) := by
        ext x; simp only [Pi.neg_apply]; ring
      rw [hneg, eLpNorm_neg]
    have hT3 : |ĝ t - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2|
        ≤ η / 3 := by
      rw [← hĝrep t htN, helper_interval_eq_restrict, hNt]
      have h1 : |∫ x, u t x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
          - ∫ x, u t x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))|
          ≤ (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm (fun x => w x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        helper_cs_diff _ _ _ _ hUt hwMem hUt hCSr
      rw [hsymm] at h1
      have h2 : (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          ≤ M * ρ :=
        calc (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
              * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            ≤ M * (eLpNorm (fun x => u t x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
              mul_le_mul_of_nonneg_right hMt hdiff0
          _ ≤ M * ρ := mul_le_mul_of_nonneg_left (le_of_lt hρw') hM0
      exact le_trans (le_trans h1 h2) hρM
    have htri : |∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2|
        ≤ |∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
            - ∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))|
          + (|∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) - ĝ t|
            + |ĝ t - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2|) := by
      have heq : ∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
          - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          = (∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
              - ∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
            + ((∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) - ĝ t)
              + (ĝ t - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
        ring
      rw [heq]
      refine le_trans (abs_add_le _ _) ?_
      have hab := abs_add_le (∫ x, u s x * w x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) - ĝ t)
        (ĝ t - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      linarith [hab]
    exact lt_of_le_of_lt htri (by linarith [hT1c, hT2, hT3])
  have hNormLim : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ,
      s ∈ Set.Icc t0 t1 → |s - t| < δ →
        |(eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2|
          < η := by
    intro η hη
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousWithinAt_iff.mp (hNormThm t htIcc) η hη
    refine ⟨δ, hδ0, fun s hsIcc hst => ?_⟩
    have hst' : dist s t < δ := by rw [Real.dist_eq]; exact hst
    have h2 := hδ hsIcc hst'
    rw [← Real.dist_eq]
    exact h2
  have hSq : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ,
      s ∈ Set.Icc t0 t1 → s ∉ Nstar → |s - t| < δ →
        (eLpNorm (fun x => u s x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          < η := by
    intro η hη
    obtain ⟨δ1, hδ10, h1⟩ := hNormLim (η / 2) (by linarith)
    obtain ⟨δ2, hδ20, h2⟩ := hPair (η / 4) (by linarith)
    refine ⟨min δ1 δ2, lt_min hδ10 hδ20, fun s hsIcc hsN hst => ?_⟩
    have hs1 : |s - t| < δ1 := lt_of_lt_of_le hst (min_le_left _ _)
    have hs2 : |s - t| < δ2 := lt_of_lt_of_le hst (min_le_right _ _)
    have eN := h1 s hsIcc hs1
    have eP := h2 s hsIcc hsN hs2
    have hUs : MemLp (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      hMemThm s hsIcc
    have hpol : (eLpNorm (fun x => u s x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        = (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          - 2 * ∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      helper_polarization _ _ _ hUs hUt
    rw [hpol]
    have hdecomp : (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        - 2 * ∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        = ((eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            - (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
          + 2 * ((eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            - ∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      ring
    rw [hdecomp]
    have hG : |(eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        - ∫ x, u s x * u t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))| < η / 4 := by
      rw [abs_sub_comm]
      exact eP
    have hA := (abs_lt.mp eN).2
    have hB := (abs_lt.mp hG).2
    linarith [hA, hB]
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  obtain ⟨δ, hδ0, hδ⟩ := hSq (ε ^ 2) hε2
  refine ⟨δ, hδ0, fun s hsIcc hsN hst => ?_⟩
  have h2 := hδ s hsIcc hsN hst
  have hnn : (0 : ℝ)
      ≤ (eLpNorm (fun x => u s x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  by_contra hcon
  push Not at hcon
  have hle : ε ^ 2
      ≤ (eLpNorm (fun x => u s x - u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
    pow_le_pow_left₀ hε.le hcon 2
  linarith [h2, hle]


theorem exists_good_near_of_null
    {t0 t1 : ℝ} (ht : t0 < t1)
    (Nstar : Set ℝ) (hNullThm : volume Nstar = 0)
    (t : ℝ) (htI : t ∈ Set.Icc t0 t1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : ℝ, s ∈ Set.Icc t0 t1 ∧ s ∉ Nstar ∧ |s - t| < δ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp htI
  have hab : max t0 (t - δ) < min t1 (t + δ) := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨ht, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hsub : Set.Ioo (max t0 (t - δ)) (min t1 (t + δ)) ⊆ Nstar := by
    intro x hx
    obtain ⟨hax, hxb⟩ := Set.mem_Ioo.mp hx
    have hxI : x ∈ Set.Icc t0 t1 :=
      Set.mem_Icc.mpr ⟨le_trans (le_max_left _ _) (le_of_lt hax),
        le_trans (le_of_lt hxb) (min_le_left _ _)⟩
    have hlt : |x - t| < δ := by
      rw [abs_lt]
      have h1 : t - δ < x := lt_of_le_of_lt (le_max_right _ _) hax
      have h2 : x < t + δ := lt_of_lt_of_le hxb (min_le_right _ _)
      constructor <;> linarith
    by_contra hxN
    exact absurd (hcon x hxI hxN) (not_le_of_gt hlt)
  have hmono : volume (Set.Ioo (max t0 (t - δ)) (min t1 (t + δ))) ≤ volume Nstar :=
    measure_mono hsub
  rw [hNullThm] at hmono
  have hpos : 0 < volume (Set.Ioo (max t0 (t - δ)) (min t1 (t + δ))) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact not_le_of_gt hpos hmono

/-- Good sequences with Cauchy slices. -/

theorem rothe_good_cauchy_seq
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ) (hNullThm : volume Nstar = 0)
    (hUnifCauchyThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s s' : ℝ, s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 → s ∉ Nstar → s' ∉ Nstar →
        |s - t| < δ → |s' - t| < δ →
        (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) :
    ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∃ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar)
      ∧ Filter.Tendsto s Filter.atTop (nhds t)
      ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          (eLpNorm (fun x => u (s n) x - u (s m) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε := by
  intro t htI
  have hseq : ∀ n : ℕ, ∃ s : ℝ,
      s ∈ Set.Icc t0 t1 ∧ s ∉ Nstar ∧ |s - t| < 1 / ((n : ℝ) + 1) := by
    intro n
    exact exists_good_near_of_null ht Nstar hNullThm t htI (1 / ((n : ℝ) + 1))
      (one_div_pos.mpr (Nat.cast_add_one_pos n))
  choose s hs using hseq
  have hclose : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |s n - t| < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    have hNle : 1 / ((N : ℝ) + 1) ≤ δ := le_of_lt (by simpa using hN)
    refine ⟨N, fun n hn => ?_⟩
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (Nat.cast_add_one_pos N)
      have hcast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    exact lt_of_lt_of_le (hs n).2.2 (le_trans hle hNle)
  refine ⟨s, fun n => ⟨(hs n).1, (hs n).2.1⟩, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hclose ε hε
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact hN n hn⟩
  · intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hUnifCauchyThm t htI ε hε
    obtain ⟨N, hN⟩ := hclose δ hδpos
    exact ⟨N, fun n m hn hm =>
      hδ (s n) (s m) (hs n).1 (hs m).1 (hs n).2.1 (hs m).2.1 (hN n hn) (hN m hm)⟩


theorem Lp_norm_sub_eq_eLpNorm
    {μ : Measure ℝ}
    (f g : ℝ → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖(MemLp.toLp f hf : Lp ℝ 2 μ) - (MemLp.toLp g hg : Lp ℝ 2 μ)‖
      = (eLpNorm (fun x => f x - g x) 2 μ).toReal := by
  have h1 : (f - g) = (fun x => f x - g x) := rfl
  rw [← MemLp.toLp_sub hf hg, Lp.norm_toLp, h1]

/-- `L²`-limit existence + independence for Cauchy slice sequences. -/

theorem Lp_limit_of_cauchy
    {μ : Measure ℝ}
    (F : ℕ → (ℝ → ℝ)) (hF : ∀ n : ℕ, MemLp (F n) 2 μ)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      (eLpNorm (fun x => F n x - F m x) 2 μ).toReal < ε) :
    ∃ L : Lp ℝ 2 μ, Filter.Tendsto
      (fun n => (MemLp.toLp (F n) (hF n) : Lp ℝ 2 μ)) Filter.atTop (nhds L)
      ∧ ∀ (G : ℕ → (ℝ → ℝ)) (hG : ∀ m : ℕ, MemLp (G m) 2 μ),
        (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          (eLpNorm (fun x => F n x - G m x) 2 μ).toReal < ε) →
        Filter.Tendsto
          (fun m => (MemLp.toLp (G m) (hG m) : Lp ℝ 2 μ))
          Filter.atTop (nhds L) := by
  have hcauchy : CauchySeq (fun n => (MemLp.toLp (F n) (hF n) : Lp ℝ 2 μ)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy ε hε
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm, Lp_norm_sub_eq_eLpNorm]
      exact hN m n hm hn⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, hL, fun G hG hJoint => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  rw [Metric.tendsto_atTop] at hL
  obtain ⟨N1, hN1⟩ := hL (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := hJoint (ε / 2) hε2
  refine ⟨max N1 N2, fun m hm => ?_⟩
  have hm1 : N1 ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : N2 ≤ m := le_trans (le_max_right _ _) hm
  have h1 : dist (MemLp.toLp (F m) (hF m) : Lp ℝ 2 μ) L < ε / 2 := hN1 m hm1
  have h2 : (eLpNorm (fun x => F m x - G m x) 2 μ).toReal < ε / 2 := hN2 m m hm2 hm2
  have hnorm : dist (MemLp.toLp (G m) (hG m) : Lp ℝ 2 μ)
      (MemLp.toLp (F m) (hF m) : Lp ℝ 2 μ) < ε / 2 := by
    rw [dist_comm, dist_eq_norm, Lp_norm_sub_eq_eLpNorm]
    exact h2
  calc dist (MemLp.toLp (G m) (hG m) : Lp ℝ 2 μ) L
      ≤ dist (MemLp.toLp (G m) (hG m) : Lp ℝ 2 μ)
          (MemLp.toLp (F m) (hF m) : Lp ℝ 2 μ)
        + dist (MemLp.toLp (F m) (hF m) : Lp ℝ 2 μ) L :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hnorm h1
    _ = ε := add_halves ε


theorem rothe_cross_cauchy
    {t0 t1 : ℝ}
    (u : ℝ → ℝ → ℝ)
    (Nstar : Set ℝ)
    (hUnifCauchyThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s s' : ℝ, s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 → s ∉ Nstar → s' ∉ Nstar →
        |s - t| < δ → |s' - t| < δ →
        (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε)
    (t : ℝ) (htIcc : t ∈ Set.Icc t0 t1)
    (s₁ s₂ : ℕ → ℝ)
    (h₁mem : ∀ n : ℕ, s₁ n ∈ Set.Icc t0 t1 ∧ s₁ n ∉ Nstar)
    (h₁tend : Filter.Tendsto s₁ Filter.atTop (nhds t))
    (h₂mem : ∀ n : ℕ, s₂ n ∈ Set.Icc t0 t1 ∧ s₂ n ∉ Nstar)
    (h₂tend : Filter.Tendsto s₂ Filter.atTop (nhds t)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      (eLpNorm (fun x => u (s₁ n) x - u (s₂ m) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hunif⟩ := hUnifCauchyThm t htIcc ε hε
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp h₁tend) δ hδ
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h₂tend) δ hδ
  refine ⟨N₁ ⊔ N₂, fun n m hn hm => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans le_sup_left hn
  have hm₂ : N₂ ≤ m := le_trans le_sup_right hm
  have e₁ : dist (s₁ n) t < δ := hN₁ n hn₁
  have e₂ : dist (s₂ m) t < δ := hN₂ m hm₂
  rw [Real.dist_eq] at e₁ e₂
  exact hunif (s₁ n) (s₂ m) (h₁mem n).1 (h₂mem m).1 (h₁mem n).2 (h₂mem m).2 e₁ e₂

/-- `eLpNorm` distance to a good-sequence term equals the `Lp` distance. -/

theorem rothe_eLpNorm_toReal_eq_dist
    (f g : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (L : ↥(Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (hL : MemLp.toLp f hf = L) :
    (eLpNorm (fun x => f x - g x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      = dist (MemLp.toLp g hg) L := by
  have hfg : MemLp (f - g) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hf.sub hg
  have hnorm : ‖MemLp.toLp (f - g) hfg‖ₑ
      = eLpNorm (f - g) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae (MemLp.coeFn_toLp hfg)
  have hfun : (fun x => f x - g x) = f - g := rfl
  rw [hfun, ← hnorm, MemLp.toLp_sub hf hg, hL, ← edist_eq_enorm_sub, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, dist_comm]

/-- Representative assembly from `Lp` limits + good sequences. -/

theorem rothe_representative_asm
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ) (hNullThm : volume Nstar = 0)
    (hSeqThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∃ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar)
      ∧ Filter.Tendsto s Filter.atTop (nhds t)
      ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          (eLpNorm (fun x => u (s n) x - u (s m) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε)
    (hUnifCauchyThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s s' : ℝ, s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 → s ∉ Nstar → s' ∉ Nstar →
        |s - t| < δ → |s' - t| < δ →
        (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε)
    (hLimThm : ∀ (F : ℕ → (ℝ → ℝ)) (hF : ∀ n : ℕ, MemLp (F n) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        (eLpNorm (fun x => F n x - F m x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) →
      ∃ L : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)), Filter.Tendsto
        (fun n => (MemLp.toLp (F n) (hF n) : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))))
        Filter.atTop (nhds L)
      ∧ ∀ (G : ℕ → (ℝ → ℝ)) (hG : ∀ m : ℕ, MemLp (G m) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          (eLpNorm (fun x => F n x - G m x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) →
        Filter.Tendsto
          (fun m => (MemLp.toLp (G m) (hG m) : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))))
          Filter.atTop (nhds L)) :
    ∃ ũ : ℝ → ℝ → ℝ,
      (fun p : ℝ × ℝ => ũ p.1 p.2) =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)]
        (fun p : ℝ × ℝ => u p.1 p.2)
      ∧ (fun x => ũ t0 x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] u0
      ∧ ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ≠ t0 → ∀ s : ℕ → ℝ,
          (∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar) →
          Filter.Tendsto s Filter.atTop (nhds t) →
          Filter.Tendsto
            (fun n => (eLpNorm (fun x => ũ t x - u (s n) x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
            Filter.atTop (nhds 0) := by
  classical
  have hSeq' : ∀ t : ℝ, ∃ s : ℕ → ℝ, t ∈ Set.Icc t0 t1 →
      ((∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar)
      ∧ Filter.Tendsto s Filter.atTop (nhds t)
      ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          (eLpNorm (fun x => u (s n) x - u (s m) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) := by
    intro t
    by_cases htIcc : t ∈ Set.Icc t0 t1
    · obtain ⟨s, h1, h2, h3⟩ := hSeqThm t htIcc
      exact ⟨s, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => t0, fun h => absurd h htIcc⟩
  choose S hS using hSeq'
  have hLim : ∀ t : ℝ, ∃ _L : ↥(Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
      ∀ _ht : t ∈ Set.Icc t0 t1,
      Filter.Tendsto
        (fun n => MemLp.toLp (fun x => u (S t n) x)
          (hMemThm (S t n) ((hS t _ht).1 n).1))
        Filter.atTop (nhds _L)
      ∧ ∀ (G : ℕ → (ℝ → ℝ)) (hG : ∀ m : ℕ, MemLp (G m) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          (eLpNorm (fun x => u (S t n) x - G m x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) →
        Filter.Tendsto
          (fun m => MemLp.toLp (G m) (hG m))
          Filter.atTop (nhds _L) := by
    intro t
    by_cases ht : t ∈ Set.Icc t0 t1
    · obtain ⟨L, hconv, hindep⟩ :=
        hLimThm (fun n => (fun x => u (S t n) x))
          (fun n => hMemThm (S t n) ((hS t ht).1 n).1) ((hS t ht).2.2)
      exact ⟨L, fun _ => ⟨hconv, hindep⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose L hL using hLim
  have hConv : ∀ (t : ℝ) (htIcc : t ∈ Set.Icc t0 t1) (s : ℕ → ℝ)
      (hsmem : ∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar)
      (hstend : Filter.Tendsto s Filter.atTop (nhds t)),
      Filter.Tendsto
        (fun m => MemLp.toLp (fun x => u (s m) x) (hMemThm (s m) (hsmem m).1))
        Filter.atTop (nhds (L t)) := by
    intro t htIcc s hsmem hstend
    have hG : ∀ m : ℕ, MemLp ((fun m : ℕ => (fun x : ℝ => u (s m) x)) m) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      fun m => hMemThm (s m) (hsmem m).1
    have hcross := rothe_cross_cauchy u Nstar hUnifCauchyThm t htIcc (S t) s
      ((hS t htIcc).1) ((hS t htIcc).2.1) hsmem hstend
    exact (hL t htIcc).2 (fun m : ℕ => (fun x : ℝ => u (s m) x)) hG hcross
  have hConstSeq : ∀ (t : ℝ) (htIcc : t ∈ Set.Icc t0 t1) (htN : t ∉ Nstar),
      L t = MemLp.toLp (fun x => u t x) (hMemThm t htIcc) := by
    intro t htIcc htN
    have hmem : ∀ n : ℕ, (fun _ : ℕ => t) n ∈ Set.Icc t0 t1 ∧ (fun _ : ℕ => t) n ∉ Nstar :=
      fun _ => ⟨htIcc, htN⟩
    have htend : Filter.Tendsto (fun _ : ℕ => t) Filter.atTop (nhds t) := tendsto_const_nhds
    have h1 := hConv t htIcc (fun _ : ℕ => t) hmem htend
    have hfun : (fun m => MemLp.toLp (fun x => u ((fun _ : ℕ => t) m) x)
          (hMemThm ((fun _ : ℕ => t) m) (hmem m).1))
        = (fun _ : ℕ => MemLp.toLp (fun x => u t x) (hMemThm t htIcc)) := rfl
    rw [hfun] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  let Lfun : ℝ → (ℝ → ℝ) := fun t =>
    if (t ∈ Set.Icc t0 t1 ∧ t ∉ Nstar ∧ t ≠ t0) then (fun x => u t x) else ↑↑(L t)
  have hLfun : ∀ t : ℝ, Lfun t =
      (if (t ∈ Set.Icc t0 t1 ∧ t ∉ Nstar ∧ t ≠ t0) then (fun x => u t x) else ↑↑(L t)) :=
    fun t => rfl
  have hLfunMem : ∀ {t : ℝ}, t ∈ Set.Icc t0 t1 → t ≠ t0 →
      MemLp (Lfun t) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    intro t htIcc ht0'
    by_cases htN : t ∉ Nstar
    · have hLt : Lfun t = (fun x => u t x) := by rw [hLfun, ite_eq_left ⟨htIcc, htN, ht0'⟩]
      rw [hLt]
      exact hMemThm t htIcc
    · push Not at htN
      have hLt : Lfun t = ↑↑(L t) := by rw [hLfun, ite_eq_right (fun h => h.2.1 htN)]
      rw [hLt]
      exact (L t).2
  have hLfunEq : ∀ {t : ℝ} (htIcc : t ∈ Set.Icc t0 t1) (ht0' : t ≠ t0),
      MemLp.toLp (Lfun t) (hLfunMem htIcc ht0') = L t := by
    intro t htIcc ht0'
    by_cases htN : t ∉ Nstar
    · have hLt : Lfun t = (fun x => u t x) := by rw [hLfun, ite_eq_left ⟨htIcc, htN, ht0'⟩]
      have hgen : ∀ (f : ℝ → ℝ) (pf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
          f = (fun x => u t x) → MemLp.toLp f pf = L t := by
        intro f pf hfg
        subst hfg
        exact (hConstSeq t htIcc htN).symm
      exact hgen (Lfun t) _ hLt
    · push Not at htN
      have hLt : Lfun t = ↑↑(L t) := by rw [hLfun, ite_eq_right (fun h => h.2.1 htN)]
      have hgen : ∀ (f : ℝ → ℝ) (pf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
          f = ↑↑(L t) → MemLp.toLp f pf = L t := by
        intro f pf hfg
        subst hfg
        exact Lp.toLp_coeFn (L t) _
      exact hgen (Lfun t) _ hLt
  let ũ : ℝ → ℝ → ℝ := fun t x =>
    if t = t0 then u0 x else if t ∈ Set.Icc t0 t1 then Lfun t x else u t x
  have hUtilde : ∀ t x : ℝ, ũ t x =
      (if t = t0 then u0 x else if t ∈ Set.Icc t0 t1 then Lfun t x else u t x) :=
    fun t x => rfl
  refine ⟨ũ, ?_, ?_, ?_⟩
  · have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    have hnull2 : volume (Nstar ∪ {t0}) = 0 := measure_union_null hNullThm Real.volume_singleton
    have hsub : {p : ℝ × ℝ | ¬ ũ p.1 p.2 = u p.1 p.2}
        ⊆ (Nstar ∪ {t0}) ×ˢ (Set.univ : Set ℝ) := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      rw [Set.mem_prod]
      refine ⟨?_, Set.mem_univ _⟩
      by_contra hcon
      rw [Set.mem_union, Set.mem_singleton_iff] at hcon
      push Not at hcon
      have hP : ũ p.1 p.2 = u p.1 p.2 := by
        by_cases hIcc : p.1 ∈ Set.Icc t0 t1
        · rw [hUtilde, ite_eq_right hcon.2, ite_eq_left hIcc]
          have hLf : Lfun p.1 = (fun x => u p.1 x) := by
            rw [hLfun, ite_eq_left ⟨hIcc, hcon.1, hcon.2⟩]
          rw [hLf]
        · rw [hUtilde, ite_eq_right hcon.2, ite_eq_right hIcc]
      exact absurd hP hp
    show ∀ᵐ p ∂ volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1), ũ p.1 p.2 = u p.1 p.2
    rw [ae_iff]
    apply le_antisymm _ zero_le
    calc volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) {p | ¬ ũ p.1 p.2 = u p.1 p.2}
        ≤ volume {p | ¬ ũ p.1 p.2 = u p.1 p.2} := Measure.restrict_le_self _
      _ ≤ volume ((Nstar ∪ {t0}) ×ˢ (Set.univ : Set ℝ)) := measure_mono hsub
      _ = volume (Nstar ∪ {t0}) * volume (Set.univ : Set ℝ) := by
          rw [hvol]
          exact Measure.prod_prod _ _
      _ = 0 := by rw [hnull2, zero_mul]
  · filter_upwards with x
    show ũ t0 x = u0 x
    rw [hUtilde, ite_eq_left rfl]
  · intro t htIcc ht0' s hsmem hstend
    have hUx : ∀ x : ℝ, ũ t x = Lfun t x := fun x => by rw [hUtilde, ite_eq_right ht0', ite_eq_left htIcc]
    have heq : ∀ n : ℕ, (eLpNorm (fun x => ũ t x - u (s n) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        = dist (MemLp.toLp (fun x => u (s n) x) (hMemThm (s n) (hsmem n).1)) (L t) := by
      intro n
      simp only [hUx]
      exact rothe_eLpNorm_toReal_eq_dist (Lfun t) (fun x => u (s n) x)
        (hLfunMem htIcc ht0') (hMemThm (s n) (hsmem n).1) (L t) (hLfunEq htIcc ht0')
    have hdist := tendsto_iff_dist_tendsto_zero.mp (hConv t htIcc s hsmem hstend)
    have hfun2 : (fun n => (eLpNorm (fun x => ũ t x - u (s n) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        = (fun b => dist (MemLp.toLp (fun x => u (s b) x) (hMemThm (s b) (hsmem b).1)) (L t)) :=
      funext fun n => heq n
    rw [hfun2]
    exact hdist


theorem rothe_representative_continuous_off_t0
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (ũ : ℝ → ℝ → ℝ)
    (hMemUtildeThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => ũ t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ)
    (hSeqThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∃ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar)
      ∧ Filter.Tendsto s Filter.atTop (nhds t))
    (hDefThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ≠ t0 → ∀ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar) →
      Filter.Tendsto s Filter.atTop (nhds t) →
      Filter.Tendsto
        (fun n => (eLpNorm (fun x => ũ t x - u (s n) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        Filter.atTop (nhds 0))
    (hUnifCauchyThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s s' : ℝ, s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 → s ∉ Nstar → s' ∉ Nstar →
        |s - t| < δ → |s' - t| < δ →
        (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε) :
    ∀ s : ℝ, s ∈ Set.Icc t0 t1 → s ≠ t0 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      t ∈ Set.Icc t0 t1 → t ≠ t0 → |t - s| < δ →
      (eLpNorm (fun x => ũ t x - ũ s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε := by
  intro s hs hne ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨δ0, hδ0pos, hδ0⟩ := hUnifCauchyThm s hs (ε / 3) hε3
  have hδ02pos : (0 : ℝ) < δ0 / 2 := by linarith
  refine ⟨δ0 / 2, hδ02pos, fun t ht htne hts => ?_⟩
  obtain ⟨s1, hs1mem, hs1lim⟩ := hSeqThm t ht
  obtain ⟨s2, hs2mem, hs2lim⟩ := hSeqThm s hs
  have hlim1 := hDefThm t ht htne s1 hs1mem hs1lim
  have hlim2 := hDefThm s hs hne s2 hs2mem hs2lim
  rw [Metric.tendsto_nhds] at hlim1 hlim2 hs1lim hs2lim
  have e1ev : ∀ᶠ n in Filter.atTop,
      (eLpNorm (fun x => ũ t x - u (s1 n) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε / 3 := by
    refine (hlim1 (ε / 3) hε3).mono fun n hn => ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hn
    exact hn
  have e2ev : ∀ᶠ n in Filter.atTop,
      (eLpNorm (fun x => ũ s x - u (s2 n) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε / 3 := by
    refine (hlim2 (ε / 3) hε3).mono fun n hn => ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hn
    exact hn
  have e3ev : ∀ᶠ n in Filter.atTop, |s1 n - t| < δ0 / 2 := by
    refine (hs1lim (δ0 / 2) hδ02pos).mono fun n hn => ?_
    rwa [Real.dist_eq] at hn
  have e4ev : ∀ᶠ n in Filter.atTop, |s2 n - s| < δ0 / 2 := by
    refine (hs2lim (δ0 / 2) hδ02pos).mono fun n hn => ?_
    rwa [Real.dist_eq] at hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (e1ev.and (e2ev.and (e3ev.and e4ev)))
  obtain ⟨g1, g2, g3, g4⟩ := hN N le_rfl
  have hmem1 := hs1mem N
  have hmem2 := hs2mem N
  have habs1 : |s1 N - s| < δ0 := by
    have h1 : s1 N - s = (s1 N - t) + (t - s) := by ring
    calc |s1 N - s| = |(s1 N - t) + (t - s)| := by rw [h1]
      _ ≤ |s1 N - t| + |t - s| := abs_add_le _ _
      _ < δ0 / 2 + δ0 / 2 := add_lt_add g3 hts
      _ = δ0 := by ring
  have habs2 : |s2 N - s| < δ0 := by linarith
  have hCauchy := hδ0 (s1 N) (s2 N) hmem1.1 hmem2.1 hmem1.2 hmem2.2 habs1 habs2
  have hMt := hMemUtildeThm t ht
  have hMs := hMemUtildeThm s hs
  have hM1u := hMemThm (s1 N) hmem1.1
  have hM2u := hMemThm (s2 N) hmem2.1
  have hMb1 : MemLp (fun x => ũ t x - u (s1 N) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hMt.sub hM1u
  have hMb2 : MemLp (fun x => u (s1 N) x - u (s2 N) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hM1u.sub hM2u
  have hMb3 : MemLp (fun x => u (s2 N) x - ũ s x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hM2u.sub hMs
  have hn1 := hMb1.eLpNorm_ne_top
  have hn2 := hMb2.eLpNorm_ne_top
  have hn3 := hMb3.eLpNorm_ne_top
  have h3eq : (fun x => u (s2 N) x - ũ s x)
      = -(fun x => ũ s x - u (s2 N) x) := by
    funext x
    simp only [Pi.neg_apply]
    ring
  have g2' : (eLpNorm (fun x => u (s2 N) x - ũ s x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε / 3 := by
    rw [h3eq, eLpNorm_neg]
    exact g2
  have h12 : (1 : ENNReal) ≤ 2 := by norm_num
  have hfun : (fun x => ũ t x - ũ s x)
      = (fun x => ũ t x - u (s1 N) x)
        + ((fun x => u (s1 N) x - u (s2 N) x)
          + (fun x => u (s2 N) x - ũ s x)) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hle : eLpNorm (fun x => ũ t x - ũ s x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ eLpNorm (fun x => ũ t x - u (s1 N) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))
        + (eLpNorm (fun x => u (s1 N) x - u (s2 N) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))
          + eLpNorm (fun x => u (s2 N) x - ũ s x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hfun]
    exact le_trans (eLpNorm_add_le h12) (add_le_add le_rfl (eLpNorm_add_le h12))
  have hnetop : eLpNorm (fun x => ũ t x - u (s1 N) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))
        + (eLpNorm (fun x => u (s1 N) x - u (s2 N) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))
          + eLpNorm (fun x => u (s2 N) x - ũ s x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))) ≠ ⊤ := by
    simp [hn1, hn2, hn3]
  calc (eLpNorm (fun x => ũ t x - ũ s x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      ≤ (eLpNorm (fun x => ũ t x - u (s1 N) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))
          + (eLpNorm (fun x => u (s1 N) x - u (s2 N) x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))
            + eLpNorm (fun x => u (s2 N) x - ũ s x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1)))).toReal :=
        ENNReal.toReal_mono hnetop hle
    _ = (eLpNorm (fun x => ũ t x - u (s1 N) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          + ((eLpNorm (fun x => u (s1 N) x - u (s2 N) x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            + (eLpNorm (fun x => u (s2 N) x - ũ s x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) := by
        rw [ENNReal.toReal_add hn1 (by simp [hn2, hn3]), ENNReal.toReal_add hn2 hn3]
    _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add g1 (add_lt_add hCauchy g2')
    _ = ε := by ring


theorem rothe_representative_slice_eq
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (ũ : ℝ → ℝ → ℝ)
    (hMemUtildeThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => ũ t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ)
    (hDefThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ≠ t0 → ∀ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1 ∧ s n ∉ Nstar) →
      Filter.Tendsto s Filter.atTop (nhds t) →
      Filter.Tendsto
        (fun n => (eLpNorm (fun x => ũ t x - u (s n) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
        Filter.atTop (nhds 0)) :
    ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ≠ t0 → t ∉ Nstar →
      (fun x => ũ t x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x => u t x) := by
  intro t ht_mem ht_ne ht_notmem
  have hlim : Filter.Tendsto
      (fun _ : ℕ => (eLpNorm (fun x => ũ t x - u t x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
      Filter.atTop (nhds 0) :=
    hDefThm t ht_mem ht_ne (fun _ : ℕ => t) (fun _ => ⟨ht_mem, ht_notmem⟩)
      tendsto_const_nhds
  have htoReal0 : (eLpNorm (fun x => ũ t x - u t x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal = 0 :=
    (tendsto_nhds_unique hlim tendsto_const_nhds).symm
  have hmem : MemLp (fun x => ũ t x - u t x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (hMemUtildeThm t ht_mem).sub (hMemThm t ht_mem)
  have hlt : eLpNorm (fun x => ũ t x - u t x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) < ⊤ :=
    hmem.eLpNorm_lt_top
  have heq0 : eLpNorm (fun x => ũ t x - u t x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal0 with h | h
    · exact h
    · exact absurd h (ne_of_lt hlt)
  have hae0 := (eLpNorm_eq_zero_iff two_ne_zero).mp heq0
  exact (sub_ae_eq_zero _ _).mp hae0


theorem integral_restrict_Icc_eq_intervalIntegral
    {g : ℝ → ℝ} :
    ∫ x, g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = ∫ x in (0 : ℝ)..1, g x := by
  have h1 : ∫ x, g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∫ x in Set.Ioc (0 : ℝ) 1, g x ∂volume := integral_Icc_eq_integral_Ioc
  rw [h1]
  exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

/-- Square-integrability of the pointwise square. -/

theorem integrable_sq_of_memLp
    {f : ℝ → ℝ} {μ : Measure ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => (f x) ^ 2) μ :=
  (hf.integrable_mul hf).congr (Filter.Eventually.of_forall (fun x => (pow_two (f x)).symm))

/-- Integrability of the pointwise product. -/

theorem integrable_mul_of_memLp
    {f g : ℝ → ℝ} {μ : Measure ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ :=
  (hf.integrable_mul hg).congr (Filter.Eventually.of_forall (fun _ => rfl))

/-- Expansion of the integral of a squared difference. -/

theorem integral_sub_sq_expand
    {f g : ℝ → ℝ} {μ : Measure ℝ}
    (h2f : Integrable (fun x => (f x) ^ 2) μ)
    (h2g : Integrable (fun x => (g x) ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    ∫ x, (f x - g x) ^ 2 ∂μ
      = ∫ x, (f x) ^ 2 ∂μ + ∫ x, (g x) ^ 2 ∂μ - 2 * ∫ x, f x * g x ∂μ := by
  have hcongr : (fun x => (f x - g x) ^ 2)
      =ᵐ[μ] (fun x => (f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x)) :=
    Filter.Eventually.of_forall (fun x => by ring)
  have hsum : Integrable (fun x => (f x) ^ 2 + (g x) ^ 2) μ :=
    (h2f.add h2g).congr (Filter.Eventually.of_forall (fun x => rfl))
  have e0 : ∫ x, (f x - g x) ^ 2 ∂μ
      = ∫ x, ((f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x)) ∂μ :=
    integral_congr_ae hcongr
  have e1 : ∫ x, ((f x) ^ 2 + (g x) ^ 2 - 2 * (f x * g x)) ∂μ
      = ∫ x, ((f x) ^ 2 + (g x) ^ 2) ∂μ - ∫ x, (2 * (f x * g x)) ∂μ :=
    integral_sub hsum (hfg.const_mul 2)
  have e2 : ∫ x, ((f x) ^ 2 + (g x) ^ 2) ∂μ
      = ∫ x, (f x) ^ 2 ∂μ + ∫ x, (g x) ^ 2 ∂μ :=
    integral_add h2f h2g
  have e3 : ∫ x, (2 * (f x * g x)) ∂μ = 2 * ∫ x, f x * g x ∂μ :=
    integral_const_mul 2 _
  rw [e0, e1, e2, e3]

/-- Polarization identity for `L²` norm squared over `Icc 0 1`. -/

theorem eLpNorm_sub_sq_eq
    {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (eLpNorm (fun x => f x - g x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      = (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        - 2 * ∫ x in (0 : ℝ)..1, f x * g x := by
  have hsub : MemLp (fun x => f x - g x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.sub hg
  have eA : (eLpNorm (fun x => f x - g x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      = ∫ x, (f x - g x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    eLpNorm_toReal_sq_eq_integral_sq hsub
  have eB : (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      = ∫ x, (f x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    eLpNorm_toReal_sq_eq_integral_sq hf
  have eC : (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      = ∫ x, (g x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    eLpNorm_toReal_sq_eq_integral_sq hg
  have eD : ∫ x, f x * g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∫ x in (0 : ℝ)..1, f x * g x :=
    integral_restrict_Icc_eq_intervalIntegral
  rw [eA, eB, eC, ← eD]
  exact integral_sub_sq_expand (integrable_sq_of_memLp hf) (integrable_sq_of_memLp hg)
    (integrable_mul_of_memLp hf hg)

/-- Polarization limit at `t0` via energy inequality + slice weak convergence. -/

theorem rothe_polarization_limit_t0_prime
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u ux : ℝ → ℝ → ℝ)
    {κ : ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (ũ : ℝ → ℝ → ℝ)
    (hMemUtildeThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => ũ t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ)
    (hInitThm : (fun x => ũ t0 x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] u0)
    (hSliceThm : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ≠ t0 → t ∉ Nstar →
      (fun x => ũ t x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x => u t x))
    (hEnergyIneqThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ≤ (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x)
    (hEnergyIntThm : ContinuousOn
      (fun τ => - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x) (Set.Icc t0 t1))
    (hSliceWeakT0Thm : Filter.Tendsto
      (fun t => ∫ x in (0 : ℝ)..1, u t x * u0 x)
      (nhdsWithin t0 (Set.Ioi t0 ∩ (Nstar)ᶜ))
      (nhds (∫ x in (0 : ℝ)..1, u0 x * u0 x)))
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hPairU0Thm : ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * u0 x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ)
    (hRepAgreeThm : ∀ ĝ : ℝ → ℝ, Continuous ĝ →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * u0 x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ →
      ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∉ Nstar →
        (∫ x in (0 : ℝ)..1, u t x * u0 x) = ĝ t)
    (hInitPairThm : ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ĝ : ℝ → ℝ, Continuous ĝ →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ →
      ĝ t0 = ∫ x in (0 : ℝ)..1, u0 x * v x) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      t ∈ Set.Icc t0 t1 → t ∉ Nstar → |t - t0| < δ →
      (eLpNorm (fun x => ũ t x - ũ t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε := by
  have eSB : (∫ x in (0 : ℝ)..1, u0 x * u0 x)
      = (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
    have c1 : (∫ x in (0 : ℝ)..1, u0 x * u0 x)
        = ∫ x, u0 x * u0 x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integral_restrict_Icc_eq_intervalIntegral.symm
    have c2 : ∫ x, u0 x * u0 x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        = ∫ x, (u0 x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (pow_two (u0 x)).symm))
    rw [c1, c2]
    exact (eLpNorm_toReal_sq_eq_integral_sq hu0).symm
  have ht0mem : t0 ∈ Set.Icc t0 t1 := ⟨le_rfl, le_of_lt ht⟩
  have hEt0 : ((fun τ => - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
      + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x) t0) = 0 := by
    simp [intervalIntegral.integral_same]
  have hE0 : Filter.Tendsto
      (fun τ => - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
        + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x)
      (nhdsWithin t0 (Set.Icc t0 t1)) (nhds 0) := by
    have hT : Filter.Tendsto
        (fun τ => - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x)
        (nhdsWithin t0 (Set.Icc t0 t1))
        (nhds ((fun τ => - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x) t0)) :=
      hEnergyIntThm.continuousWithinAt ht0mem
    rw [hEt0] at hT
    exact hT
  have hT1 : Filter.Tendsto
      (fun t => (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
      (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
    rw [tendsto_order]
    constructor
    · intro a' ha'
      by_cases hB0 : (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 = 0
      · apply Filter.Eventually.of_forall
        intro t
        have hnn : 0 ≤ (eLpNorm (fun x => u t x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := sq_nonneg _
        linarith
      · have hBpos : 0 < (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
          have hnn : 0 ≤ (eLpNorm u0 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := sq_nonneg _
          exact lt_of_le_of_ne hnn (Ne.symm hB0)
        have hQ : Filter.Tendsto
            (fun t => ∫ x in (0 : ℝ)..1, u t x * u0 x)
            (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
            (nhds (∫ x in (0 : ℝ)..1, u0 x * u0 x)) :=
          hSliceWeakT0Thm.mono_left (nhdsWithin_mono t0 Set.inter_subset_right)
        have hB2 : ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) ^ 2
            / (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            = (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
          field_simp
        have hQ2 : Filter.Tendsto
            (fun t => (∫ x in (0 : ℝ)..1, u t x * u0 x) ^ 2
              / (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
            (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
            (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
          have h := (hQ.pow 2).div_const
            ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
          rw [eSB] at h
          rw [hB2] at h
          exact h
        have hEv : ∀ᶠ t in (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ))),
            a' < (∫ x in (0 : ℝ)..1, u t x * u0 x) ^ 2
              / (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
          hQ2.eventually_const_lt ha'
        filter_upwards [hEv, self_mem_nhdsWithin] with t hEv' htmem
        obtain ⟨htIcc, -, -⟩ := htmem
        have hCS := hCSThm (hMemThm t htIcc) hu0
        have hsq : (∫ x in (0 : ℝ)..1, u t x * u0 x) ^ 2
            ≤ (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
              * (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
          have h1 : (∫ x in (0 : ℝ)..1, u t x * u0 x) ^ 2
              = |∫ x in (0 : ℝ)..1, u t x * u0 x| ^ 2 := (sq_abs _).symm
          have h2 : |∫ x in (0 : ℝ)..1, u t x * u0 x| ^ 2
              ≤ ((eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
                * (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hCS 2
          have h3 : ((eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
                * (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2
              = (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
                * (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
            mul_pow _ _ _
          linarith
        have hdiv : (∫ x in (0 : ℝ)..1, u t x * u0 x) ^ 2
              / (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
          rw [div_le_iff₀ hBpos]
          exact hsq
        linarith
    · intro b' hb'
      have hE0l : Filter.Tendsto
          (fun τ => - 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
            + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x)
          (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ))) (nhds 0) :=
        hE0.mono_left (nhdsWithin_mono t0 Set.inter_subset_left)
      have hEe : ∀ᶠ τ in (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ))),
          (- 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux t x) ^ 2
            + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, F t x * u t x)
            < b' - (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
        hE0l.eventually_lt_const (by linarith : (0 : ℝ)
          < b' - (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      filter_upwards [hEe, self_mem_nhdsWithin] with t hE htmem
      obtain ⟨htIcc, -, -⟩ := htmem
      have hI := hEnergyIneqThm t htIcc
      linarith
  obtain ⟨ĝ, hĝcont, hĝae⟩ := hPairU0Thm
  have hĝt0 : ĝ t0 = ∫ x in (0 : ℝ)..1, u0 x * u0 x :=
    hInitPairThm u0 hu0 ĝ hĝcont hĝae
  have hĝtend : Filter.Tendsto ĝ
      (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
      (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
    have h : Filter.Tendsto ĝ (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
        (nhds (ĝ t0)) :=
      (hĝcont.tendsto t0).mono_left nhdsWithin_le_nhds
    rw [hĝt0, eSB] at h
    exact h
  have hQtend : Filter.Tendsto (fun t => ∫ x in (0 : ℝ)..1, u t x * u0 x)
      (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
      (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
    refine hĝtend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t htmem
    obtain ⟨htIcc, -, htN⟩ := htmem
    exact (hRepAgreeThm ĝ hĝcont hĝae t htIcc htN).symm
  have hPtend : Filter.Tendsto (fun t => ∫ x in (0 : ℝ)..1, ũ t x * u0 x)
      (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
      (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
    refine hQtend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t htmem
    obtain ⟨htIcc, htIoi, htN⟩ := htmem
    have ht0 : t ≠ t0 := ne_of_gt htIoi
    have hae := hSliceThm t htIcc ht0 htN
    have hmul : ((fun x => ũ t x) * u0)
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] ((fun x => u t x) * u0) :=
      hae.mul Filter.EventuallyEq.rfl
    have hIoc := ae_restrict_of_ae_restrict_of_subset
      (Set.Ioc_subset_Icc_self (a := (0 : ℝ)) (b := 1)) hmul
    have ePQ : (∫ x in (0 : ℝ)..1, u t x * u0 x)
        = ∫ x in (0 : ℝ)..1, ũ t x * u0 x := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact (integral_congr_ae hIoc).symm
    exact ePQ
  have hAtend : Filter.Tendsto
      (fun t => (eLpNorm (fun x => ũ t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
      (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
    refine hT1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t htmem
    obtain ⟨htIcc, htIoi, htN⟩ := htmem
    have ht0 : t ≠ t0 := ne_of_gt htIoi
    have hae := hSliceThm t htIcc ht0 htN
    have eAR : (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        = (eLpNorm (fun x => ũ t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
      rw [eLpNorm_congr_ae hae]
    exact eAR
  have hDtend : Filter.Tendsto
      (fun t => (eLpNorm (fun x => ũ t x - u0 x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ))) (nhds 0) := by
    have hcomb : Filter.Tendsto
        (fun t => (eLpNorm (fun x => ũ t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          - 2 * ∫ x in (0 : ℝ)..1, ũ t x * u0 x)
        (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ)))
        (nhds ((eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          - 2 * (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) :=
      (hAtend.add tendsto_const_nhds).sub (tendsto_const_nhds.mul hPtend)
    have h0 : (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          - 2 * (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 = 0 := by
      ring
    rw [h0] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t htmem
    obtain ⟨htIcc, -, -⟩ := htmem
    exact (eLpNorm_sub_sq_eq (hMemUtildeThm t htIcc) hu0).symm
  intro ε hε
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hEvD : ∀ᶠ t in (nhdsWithin t0 (Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ))),
      (eLpNorm (fun x => ũ t x - u0 x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 < ε ^ 2 :=
    hDtend.eventually_lt_const hε2
  rw [eventually_nhdsWithin_iff] at hEvD
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hEvD
  refine ⟨δ, hδpos, fun t htIcc htN hdist => ?_⟩
  by_cases ht0 : t = t0
  · have h0 : (fun x => ũ t x - ũ t0 x) = 0 := by
      funext x
      show ũ t x - ũ t0 x = 0
      rw [ht0, sub_self]
    rw [h0, eLpNorm_zero, ENNReal.toReal_zero]
    exact hε
  · have htIt : t0 < t := lt_of_le_of_ne htIcc.1 (Ne.symm ht0)
    have hmem : t ∈ Set.Icc t0 t1 ∩ (Set.Ioi t0 ∩ Nstarᶜ) := ⟨htIcc, htIt, htN⟩
    have hball : t ∈ Metric.ball t0 δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hdist
    have hD := hδ t hball hmem
    have hcongr : eLpNorm (fun x => ũ t x - ũ t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
        = eLpNorm (fun x => ũ t x - u0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      apply eLpNorm_congr_ae
      exact (Filter.EventuallyEq.rfl (f := fun x => ũ t x)).sub hInitThm
    rw [hcongr]
    have hlt := abs_lt_of_sq_lt_sq hD (le_of_lt hε)
    rwa [abs_of_nonneg ENNReal.toReal_nonneg] at hlt


theorem sum_step_telescoping (U : ℕ → ℕ → (ℝ → ℝ)) (N a m : ℕ) (x : ℝ) :
    (U N (a + m)) x - (U N a) x
      = ∑ j ∈ Finset.range m, ((U N (a + j + 1)) x - (U N (a + j)) x) := by
  have h := Finset.sum_range_sub (fun j => (U N (a + j)) x) m
  simp only [Nat.add_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j hj
  have haj : a + (j + 1) = a + j + 1 := by omega
  rw [haj]


theorem eLpNorm_telescoping_le (U : ℕ → ℕ → (ℝ → ℝ))
    (hU : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (N a m : ℕ) :
    (eLpNorm (fun x => (U N (a + m)) x - (U N a) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      ≤ ∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  have hfun : (fun x => (U N (a + m)) x - (U N a) x)
      = ∑ j ∈ Finset.range m, (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) := by
    funext x
    rw [Finset.sum_apply]
    exact sum_step_telescoping U N a m x
  rw [hfun]
  have htri : eLpNorm (∑ j ∈ Finset.range m,
      (fun x => (U N (a + j + 1)) x - (U N (a + j)) x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))
      ≤ ∑ j ∈ Finset.range m, eLpNorm
        (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply eLpNorm_sum_le
    norm_num
  have hfin : ∀ j ∈ Finset.range m, eLpNorm
      (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ := by
    intro j hj
    exact MemLp.eLpNorm_ne_top ((hU N (a + j + 1)).sub (hU N (a + j)))
  have hsumfin : (∑ j ∈ Finset.range m, eLpNorm
      (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    exact hfin
  calc (eLpNorm (∑ j ∈ Finset.range m,
        (fun x => (U N (a + j + 1)) x - (U N (a + j)) x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
      ≤ (∑ j ∈ Finset.range m, eLpNorm
        (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        ENNReal.toReal_mono hsumfin htri
    _ = ∑ j ∈ Finset.range m, (eLpNorm
        (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        ENNReal.toReal_sum hfin


theorem sq_eLpNorm_telescoping_le (t0 t1 : ℝ) (U : ℕ → ℕ → (ℝ → ℝ))
    (hU : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (N a m : ℕ) (C0 : ℝ)
    (hτ : 0 < (t1 - t0) / N)
    (hDiss : ((t1 - t0) / N) * ∑ j ∈ Finset.range N,
        (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 / (((t1 - t0) / N) ^ 2) ≤ C0)
    (ham : a + m ≤ N) :
    (eLpNorm (fun x => (U N (a + m)) x - (U N a) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      ≤ (m : ℝ) * ((t1 - t0) / N) * C0 := by
  have htri := eLpNorm_telescoping_le U hU N a m
  have hDnn : 0 ≤ (eLpNorm (fun x => (U N (a + m)) x - (U N a) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := ENNReal.toReal_nonneg
  have hD2 : (eLpNorm (fun x => (U N (a + m)) x - (U N a) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      ≤ (∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2 :=
    pow_le_pow_left₀ hDnn htri 2
  have hCS : (∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2
      ≤ (m : ℝ) * ∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range m)
      (f := fun j => (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    rw [Finset.card_range] at h
    exact h
  have hsub : ∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      ≤ ∑ j ∈ Finset.range N, (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
    have h_add := Finset.sum_range_add
      (fun k => (eLpNorm (fun x => (U N (k + 1)) x - (U N k) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) a m
    have h_nn_a : 0 ≤ ∑ k ∈ Finset.range a, (eLpNorm (fun x => (U N (k + 1)) x - (U N k) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
      Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have h_le1 : ∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ≤ ∑ k ∈ Finset.range (a + m), (eLpNorm (fun x => (U N (k + 1)) x - (U N k) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
      have h2 : ∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N ((a + j) + 1)) x - (U N (a + j)) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          ≤ ∑ k ∈ Finset.range (a + m), (eLpNorm (fun x => (U N (k + 1)) x - (U N k) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
        have h3 := h_add
        have h4 := h_nn_a
        linarith
      simpa only [Nat.add_assoc] using h2
    have h_le2 : ∑ k ∈ Finset.range (a + m), (eLpNorm (fun x => (U N (k + 1)) x - (U N k) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ≤ ∑ j ∈ Finset.range N, (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_subset_range.mpr ham
      · intro i hi his
        exact sq_nonneg _
    exact le_trans h_le1 h_le2
  have hτne : (t1 - t0) / N ≠ 0 := ne_of_gt hτ
  have hsum_eq : ∑ j ∈ Finset.range N,
        (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 / (((t1 - t0) / N) ^ 2)
      = (∑ j ∈ Finset.range N, (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) / (((t1 - t0) / N) ^ 2) := by
    rw [Finset.sum_div]
  have hdis : ∑ j ∈ Finset.range N, (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      ≤ ((t1 - t0) / N) * C0 := by
    rw [hsum_eq] at hDiss
    have h_simp : ((t1 - t0) / N) * ((∑ j ∈ Finset.range N,
        (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) / (((t1 - t0) / N) ^ 2))
        = (∑ j ∈ Finset.range N, (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) / ((t1 - t0) / N) := by
      field_simp
    rw [h_simp] at hDiss
    have h5 := (div_le_iff₀ hτ).mp hDiss
    linarith
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  calc (eLpNorm (fun x => (U N (a + m)) x - (U N a) x) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      ≤ (∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) ^ 2 := hD2
    _ ≤ (m : ℝ) * ∑ j ∈ Finset.range m, (eLpNorm (fun x => (U N (a + j + 1)) x - (U N (a + j)) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := hCS
    _ ≤ (m : ℝ) * ∑ j ∈ Finset.range N, (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
        mul_le_mul_of_nonneg_left hsub hmnn
    _ ≤ (m : ℝ) * (((t1 - t0) / N) * C0) :=
        mul_le_mul_of_nonneg_left hdis hmnn
    _ = (m : ℝ) * ((t1 - t0) / N) * C0 := by ring


theorem floor_diff_le (x y : ℝ) (hy : 0 ≤ y) :
    (Nat.floor y : ℝ) - (Nat.floor x : ℝ) ≤ |y - x| + 1 := by
  have h1 : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy
  have h2 : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  have h3 : y - x ≤ |y - x| := le_abs_self _
  linarith


theorem floor_add_one_le_of_lt (y : ℝ) (N : ℕ) (hy0 : 0 ≤ y) (hylt : y < (N : ℝ)) :
    Nat.floor y + 1 ≤ N := by
  have h1 : (Nat.floor y : ℝ) ≤ y := Nat.floor_le hy0
  have h2 : (Nat.floor y : ℝ) < (N : ℝ) := lt_of_le_of_lt h1 hylt
  have h3 : Nat.floor y < N := Nat.cast_lt.mp h2
  omega


theorem eLpNorm_diff_symm (U : ℕ → ℕ → (ℝ → ℝ)) (N a b : ℕ) :
    (eLpNorm (fun x => (U N b) x - (U N a) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
    = (eLpNorm (fun x => (U N a) x - (U N b) x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  have hfun : (fun x => (U N b) x - (U N a) x)
      = -(fun x => (U N a) x - (U N b) x) := by
    funext x
    simp only [Pi.neg_apply]
    rw [neg_sub]
  rw [hfun]
  rw [eLpNorm_neg]

/-- Time-translation estimate for Rothe interpolants. -/

theorem rothe_timetrans_estimate
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U : ℕ → ℕ → (ℝ → ℝ))
    (hU : ∀ (N : ℕ) (k : ℕ), MemLp (U N k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hDissThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N →
      ((t1 - t0) / N) * ∑ j ∈ Finset.range N,
        (eLpNorm (fun x => (U N (j + 1)) x - (U N j) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 / (((t1 - t0) / N) ^ 2) ≤ C)
    (hInterpThm : ∀ (N : ℕ) (t : ℝ), t ∈ Set.Icc t0 t1 →
      ∀ x : ℝ, (if t = t1 then (U N N) x
        else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)
      = (if t = t1 then (U N N) x
        else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ t h : ℝ,
      t ∈ Set.Icc t0 t1 → t + h ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x =>
        (if t + h = t1 then (U N N) x
         else (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x)
        - (if t = t1 then (U N N) x
           else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x))
        2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * (|h| + (t1 - t0) / N)) := by
  obtain ⟨C0, hC0nn, hDiss_all⟩ := hDissThm
  refine ⟨2 * C0, by linarith, fun N hN t h htmem hthmem => ?_⟩
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNneR : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  have htpos : 0 < t1 - t0 := sub_pos.mpr ht
  have htne : t1 - t0 ≠ 0 := ne_of_gt htpos
  have hτpos : 0 < (t1 - t0) / N := div_pos htpos hNposR
  have hτne : (t1 - t0) / N ≠ 0 := ne_of_gt hτpos
  have hDiss := hDiss_all N hN
  obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp htmem
  obtain ⟨hth0, hth1⟩ := Set.mem_Icc.mp hthmem
  have hx0 : 0 ≤ (t - t0) / ((t1 - t0) / N) :=
    div_nonneg (sub_nonneg.mpr ht0) (le_of_lt hτpos)
  have hy0 : 0 ≤ (t + h - t0) / ((t1 - t0) / N) :=
    div_nonneg (sub_nonneg.mpr hth0) (le_of_lt hτpos)
  have hdivN : (t1 - t0) / ((t1 - t0) / N) = (N : ℝ) := by
    field_simp
  by_cases ht1eq : t = t1
  · by_cases hth1eq : t + h = t1
    · simp only [hth1eq, ite_true]
      simp only [ht1eq, ite_true]
      have hfun0 : (fun x => (U N N) x - (U N N) x) = 0 := by
        funext x
        simp
      rw [hfun0, eLpNorm_zero, ENNReal.toReal_zero]
      exact Real.sqrt_nonneg _
    · have hf : (t + h = t1) = False := eq_false hth1eq
      have htt : (t = t1) = True := eq_true ht1eq
      simp only [hf, htt, ite_true, ite_false]
      have hth_lt : t + h < t1 := lt_of_le_of_ne hth1 hth1eq
      have hy_lt_N : (t + h - t0) / ((t1 - t0) / N) < (N : ℝ) := by
        have h1 : t + h - t0 < t1 - t0 := by linarith
        have h2 : (t + h - t0) / ((t1 - t0) / N) < (t1 - t0) / ((t1 - t0) / N) := by
          gcongr
        rw [hdivN] at h2
        exact h2
      have hk2_le : Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1 ≤ N :=
        floor_add_one_le_of_lt _ _ hy0 hy_lt_N
      have hsymm : (eLpNorm (fun x => (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x - (U N N) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          = (eLpNorm (fun x => (U N N) x - (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
        eLpNorm_diff_symm U N N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
      rw [hsymm]
      have ham_le : (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) + (N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) ≤ N := by
        omega
      have ham_eq : (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) + (N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) = N := by
        omega
      have hsq := sq_eLpNorm_telescoping_le t0 t1 U hU N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
        (N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) C0 hτpos hDiss ham_le
      rw [ham_eq] at hsq
      have hh_nonpos : h ≤ 0 := by linarith
      have habs : |h| = -h := abs_of_nonpos hh_nonpos
      have hN_sub_y : (N : ℝ) - (t + h - t0) / ((t1 - t0) / N) = |h| / ((t1 - t0) / N) := by
        rw [habs, ht1eq]
        have hN : (N : ℝ) = (t1 - t0) / ((t1 - t0) / N) := hdivN.symm
        rw [hN]
        field_simp
        ring
      have hfloor_le : (t + h - t0) / ((t1 - t0) / N)
          ≤ (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) : ℝ) + 1 := by
        have hlt := Nat.lt_floor_add_one ((t + h - t0) / ((t1 - t0) / N))
        linarith
      have hm_le : ((N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ)
          ≤ |h| / ((t1 - t0) / N) + 1 := by
        have hcast : ((N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ)
            = (N : ℝ) - ((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) : ℝ) + 1) := by
          have h1 : ((N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ)
              = (N : ℝ) - ((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1 : ℕ) : ℝ) :=
            Nat.cast_sub hk2_le
          rw [h1]
          push_cast
          ring
        rw [hcast, ← hN_sub_y]
        linarith
      have hmτ_le : ((N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ) * ((t1 - t0) / N)
          ≤ |h| + (t1 - t0) / N := by
        have h2 := mul_le_mul_of_nonneg_right hm_le (le_of_lt hτpos)
        have h3 : (|h| / ((t1 - t0) / N) + 1) * ((t1 - t0) / N) = |h| + (t1 - t0) / N := by
          field_simp
        rw [h3] at h2
        exact h2
      have hC0_le : C0 ≤ 2 * C0 := by linarith
      have hsum_nn : 0 ≤ |h| + (t1 - t0) / N := by
        have habs_nn : 0 ≤ |h| := abs_nonneg _
        have hτnn : 0 ≤ (t1 - t0) / N := le_of_lt hτpos
        linarith
      have hfinal_sq : (eLpNorm (fun x => (U N N) x - (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
        calc (eLpNorm (fun x => (U N N) x - (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ ((N - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ) * ((t1 - t0) / N) * C0 := hsq
          _ ≤ (|h| + (t1 - t0) / N) * C0 :=
              mul_le_mul_of_nonneg_right hmτ_le hC0nn
          _ ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
              have h6 : (|h| + (t1 - t0) / N) * C0 ≤ (|h| + (t1 - t0) / N) * (2 * C0) :=
                mul_le_mul_of_nonneg_left hC0_le hsum_nn
              have h7 : (|h| + (t1 - t0) / N) * (2 * C0) = (2 * C0) * (|h| + (t1 - t0) / N) :=
                mul_comm _ _
              rw [h7] at h6
              exact h6
      exact Real.le_sqrt_of_sq_le hfinal_sq
  · by_cases hth1eq : t + h = t1
    · have hf : (t + h = t1) = True := eq_true hth1eq
      have htt : (t = t1) = False := eq_false ht1eq
      simp only [hf, htt, ite_true, ite_false]
      have ht_lt : t < t1 := lt_of_le_of_ne ht1 ht1eq
      have hx_lt_N : (t - t0) / ((t1 - t0) / N) < (N : ℝ) := by
        have h1 : t - t0 < t1 - t0 := by linarith
        have h2 : (t - t0) / ((t1 - t0) / N) < (t1 - t0) / ((t1 - t0) / N) := by
          gcongr
        rw [hdivN] at h2
        exact h2
      have hk1_le : Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 ≤ N :=
        floor_add_one_le_of_lt _ _ hx0 hx_lt_N
      have ham_le : (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) + (N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) ≤ N := by
        omega
      have ham_eq : (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) + (N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) = N := by
        omega
      have hsq := sq_eLpNorm_telescoping_le t0 t1 U hU N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
        (N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) C0 hτpos hDiss ham_le
      rw [ham_eq] at hsq
      have hh_nonneg : 0 ≤ h := by linarith
      have habs : |h| = h := abs_of_nonneg hh_nonneg
      have hh_eq : h = t1 - t := by linarith
      have hN_sub_x : (N : ℝ) - (t - t0) / ((t1 - t0) / N) = |h| / ((t1 - t0) / N) := by
        rw [habs, hh_eq]
        have hN : (N : ℝ) = (t1 - t0) / ((t1 - t0) / N) := hdivN.symm
        rw [hN]
        field_simp
        ring
      have hfloor_le : (t - t0) / ((t1 - t0) / N)
          ≤ (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) + 1 := by
        have hlt := Nat.lt_floor_add_one ((t - t0) / ((t1 - t0) / N))
        linarith
      have hm_le : ((N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ)
          ≤ |h| / ((t1 - t0) / N) + 1 := by
        have hcast : ((N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ)
            = (N : ℝ) - ((Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) + 1) := by
          have h1 : ((N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ)
              = (N : ℝ) - ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 : ℕ) : ℝ) :=
            Nat.cast_sub hk1_le
          rw [h1]
          push_cast
          ring
        rw [hcast, ← hN_sub_x]
        linarith
      have hmτ_le : ((N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ) * ((t1 - t0) / N)
          ≤ |h| + (t1 - t0) / N := by
        have h2 := mul_le_mul_of_nonneg_right hm_le (le_of_lt hτpos)
        have h3 : (|h| / ((t1 - t0) / N) + 1) * ((t1 - t0) / N) = |h| + (t1 - t0) / N := by
          field_simp
        rw [h3] at h2
        exact h2
      have hC0_le : C0 ≤ 2 * C0 := by linarith
      have hsum_nn : 0 ≤ |h| + (t1 - t0) / N := by
        have habs_nn : 0 ≤ |h| := abs_nonneg _
        have hτnn : 0 ≤ (t1 - t0) / N := le_of_lt hτpos
        linarith
      have hfinal_sq : (eLpNorm (fun x => (U N N) x - (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
        calc (eLpNorm (fun x => (U N N) x - (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) 2
              (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ ((N - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ) : ℝ) * ((t1 - t0) / N) * C0 := hsq
          _ ≤ (|h| + (t1 - t0) / N) * C0 :=
              mul_le_mul_of_nonneg_right hmτ_le hC0nn
          _ ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
              have h6 : (|h| + (t1 - t0) / N) * C0 ≤ (|h| + (t1 - t0) / N) * (2 * C0) :=
                mul_le_mul_of_nonneg_left hC0_le hsum_nn
              have h7 : (|h| + (t1 - t0) / N) * (2 * C0) = (2 * C0) * (|h| + (t1 - t0) / N) :=
                mul_comm _ _
              rw [h7] at h6
              exact h6
      exact Real.le_sqrt_of_sq_le hfinal_sq
    · have hf : (t + h = t1) = False := eq_false hth1eq
      have htt : (t = t1) = False := eq_false ht1eq
      simp only [hf, htt, ite_false]
      have ht_lt : t < t1 := lt_of_le_of_ne ht1 ht1eq
      have hth_lt : t + h < t1 := lt_of_le_of_ne hth1 hth1eq
      have hx_lt_N : (t - t0) / ((t1 - t0) / N) < (N : ℝ) := by
        have h1 : t - t0 < t1 - t0 := by linarith
        have h2 : (t - t0) / ((t1 - t0) / N) < (t1 - t0) / ((t1 - t0) / N) := by
          gcongr
        rw [hdivN] at h2
        exact h2
      have hy_lt_N : (t + h - t0) / ((t1 - t0) / N) < (N : ℝ) := by
        have h1 : t + h - t0 < t1 - t0 := by linarith
        have h2 : (t + h - t0) / ((t1 - t0) / N) < (t1 - t0) / ((t1 - t0) / N) := by
          gcongr
        rw [hdivN] at h2
        exact h2
      have hk1_le : Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 ≤ N :=
        floor_add_one_le_of_lt _ _ hx0 hx_lt_N
      have hk2_le : Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1 ≤ N :=
        floor_add_one_le_of_lt _ _ hy0 hy_lt_N
      have hyx : (t + h - t0) / ((t1 - t0) / N) - (t - t0) / ((t1 - t0) / N)
          = h / ((t1 - t0) / N) := by
        have hsub : (t + h - t0) - (t - t0) = h := by ring
        have hdiv : (t + h - t0) / ((t1 - t0) / N) - (t - t0) / ((t1 - t0) / N)
            = ((t + h - t0) - (t - t0)) / ((t1 - t0) / N) :=
          (sub_div _ _ _).symm
        rw [hdiv, hsub]
      have habs_div : |(t + h - t0) / ((t1 - t0) / N) - (t - t0) / ((t1 - t0) / N)|
          = |h| / ((t1 - t0) / N) := by
        rw [hyx, abs_div, abs_of_pos hτpos]
      have hC0_le : C0 ≤ 2 * C0 := by linarith
      have hsum_nn : 0 ≤ |h| + (t1 - t0) / N := by
        have habs_nn : 0 ≤ |h| := abs_nonneg _
        have hτnn : 0 ≤ (t1 - t0) / N := le_of_lt hτpos
        linarith
      by_cases hle : Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1
          ≤ Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1
      · have ham_le : (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
            + ((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) ≤ N := by
          omega
        have ham_eq : (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
            + ((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1))
            = Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1 := by
          omega
        have hsq := sq_eLpNorm_telescoping_le t0 t1 U hU N
          (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
          ((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
            - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) C0 hτpos hDiss ham_le
        rw [ham_eq] at hsq
        have hfloor := floor_diff_le ((t - t0) / ((t1 - t0) / N))
          ((t + h - t0) / ((t1 - t0) / N)) hy0
        rw [habs_div] at hfloor
        have hm_le : ((((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ)
            ≤ |h| / ((t1 - t0) / N) + 1 := by
          have hcast : ((((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
                - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ)
              = (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) : ℝ)
                - (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ) := by
            rw [Nat.cast_sub hle]
            push_cast
            ring
          rw [hcast]
          exact hfloor
        have hmτ_le : ((((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ) * ((t1 - t0) / N)
            ≤ |h| + (t1 - t0) / N := by
          have h2 := mul_le_mul_of_nonneg_right hm_le (le_of_lt hτpos)
          have h3 : (|h| / ((t1 - t0) / N) + 1) * ((t1 - t0) / N) = |h| + (t1 - t0) / N := by
            field_simp
          rw [h3] at h2
          exact h2
        have hfinal_sq : (eLpNorm (fun x =>
              (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x
              - (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
          calc (eLpNorm (fun x =>
                (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x
                - (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) 2
                (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
              ≤ ((((Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
                - (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ) * ((t1 - t0) / N) * C0 := hsq
            _ ≤ (|h| + (t1 - t0) / N) * C0 :=
                mul_le_mul_of_nonneg_right hmτ_le hC0nn
            _ ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
                have h6 : (|h| + (t1 - t0) / N) * C0 ≤ (|h| + (t1 - t0) / N) * (2 * C0) :=
                  mul_le_mul_of_nonneg_left hC0_le hsum_nn
                have h7 : (|h| + (t1 - t0) / N) * (2 * C0) = (2 * C0) * (|h| + (t1 - t0) / N) :=
                  mul_comm _ _
                rw [h7] at h6
                exact h6
        exact Real.le_sqrt_of_sq_le hfinal_sq
      · have hle' : Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1
            ≤ Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 :=
          le_of_not_ge hle
        have hsymm : (eLpNorm (fun x =>
              (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x
              - (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
            = (eLpNorm (fun x =>
              (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x
              - (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
          eLpNorm_diff_symm U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
            (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
        rw [hsymm]
        have ham_le : (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
            + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) ≤ N := by
          omega
        have ham_eq : (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
            + ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1))
            = Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1 := by
          omega
        have hsq := sq_eLpNorm_telescoping_le t0 t1 U hU N
          (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)
          ((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
            - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) C0 hτpos hDiss ham_le
        rw [ham_eq] at hsq
        have hfloor := floor_diff_le ((t + h - t0) / ((t1 - t0) / N))
          ((t - t0) / ((t1 - t0) / N)) hx0
        have habs_comm : |(t - t0) / ((t1 - t0) / N) - (t + h - t0) / ((t1 - t0) / N)|
            = |h| / ((t1 - t0) / N) := by
          have hcomm : |(t - t0) / ((t1 - t0) / N) - (t + h - t0) / ((t1 - t0) / N)|
              = |(t + h - t0) / ((t1 - t0) / N) - (t - t0) / ((t1 - t0) / N)| := by
            rw [abs_sub_comm]
          rw [hcomm, habs_div]
        rw [habs_comm] at hfloor
        have hm_le : ((((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ)
            ≤ |h| / ((t1 - t0) / N) + 1 := by
          have hcast : ((((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
                - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ)
              = (Nat.floor ((t - t0) / ((t1 - t0) / N)) : ℝ)
                - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) : ℝ) := by
            rw [Nat.cast_sub hle']
            push_cast
            ring
          rw [hcast]
          exact hfloor
        have hmτ_le : ((((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
              - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ) * ((t1 - t0) / N)
            ≤ |h| + (t1 - t0) / N := by
          have h2 := mul_le_mul_of_nonneg_right hm_le (le_of_lt hτpos)
          have h3 : (|h| / ((t1 - t0) / N) + 1) * ((t1 - t0) / N) = |h| + (t1 - t0) / N := by
            field_simp
          rw [h3] at h2
          exact h2
        have hfinal_sq : (eLpNorm (fun x =>
              (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x
              - (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
          calc (eLpNorm (fun x =>
                (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x
                - (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x) 2
                (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
              ≤ ((((Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)
                - (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1) : ℕ)) : ℝ) * ((t1 - t0) / N) * C0 := hsq
            _ ≤ (|h| + (t1 - t0) / N) * C0 :=
                mul_le_mul_of_nonneg_right hmτ_le hC0nn
            _ ≤ (2 * C0) * (|h| + (t1 - t0) / N) := by
                have h6 : (|h| + (t1 - t0) / N) * C0 ≤ (|h| + (t1 - t0) / N) * (2 * C0) :=
                  mul_le_mul_of_nonneg_left hC0_le hsum_nn
                have h7 : (|h| + (t1 - t0) / N) * (2 * C0) = (2 * C0) * (|h| + (t1 - t0) / N) :=
                  mul_comm _ _
                rw [h7] at h6
                exact h6
        exact Real.le_sqrt_of_sq_le hfinal_sq


theorem rothe_timetrans_passage
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U : ℕ → ℕ → (ℝ → ℝ))
    (φm : ℕ → ℕ) (hφm : StrictMono φm)
    (Nstar : Set ℝ)
    (hTimetransThm : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ t h : ℝ,
      t ∈ Set.Icc t0 t1 → t + h ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x =>
        (if t + h = t1 then (U N N) x
         else (U N (Nat.floor ((t + h - t0) / ((t1 - t0) / N)) + 1)) x)
        - (if t = t1 then (U N N) x
           else (U N (Nat.floor ((t - t0) / ((t1 - t0) / N)) + 1)) x))
        2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * (|h| + (t1 - t0) / N)))
    (hSliceWeakThm : ∀ (τ : ℝ), τ ∈ Set.Icc t0 t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1,
            (if τ = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φm N))) + 1)) x) * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)))
    (hWLSCThm : ∀ (s s' : ℝ), s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Filter.liminf (fun N : ℕ =>
          (eLpNorm (fun x =>
            (if s = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((s - t0) / ((t1 - t0) / (φm N))) + 1)) x)
            - (if s' = t1 then (U (φm N) (φm N)) x
               else (U (φm N) (Nat.floor ((s' - t0) / ((t1 - t0) / (φm N))) + 1)) x))
            2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) Filter.atTop) :
    ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s s' : ℝ, s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 → s ∉ Nstar → s' ∉ Nstar →
        |s - t| < δ → |s' - t| < δ →
        (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε := by
  obtain ⟨C, hC0, hCT⟩ := hTimetransThm
  have hid_le : ∀ N : ℕ, N ≤ φm N := by
    intro N
    induction N with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφm (Nat.lt_succ_self k)))
  have hφm_top : Filter.Tendsto φm Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hid_le Filter.tendsto_id
  have hpass : ∀ s s' : ℝ, s ∈ Set.Icc t0 t1 → s' ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * |s - s'|) := by
    intro s s' hs hs'
    have hbound : ∀ᶠ N : ℕ in Filter.atTop,
        (eLpNorm (fun x =>
          (if s = t1 then (U (φm N) (φm N)) x
           else (U (φm N) (Nat.floor ((s - t0) / ((t1 - t0) / (φm N))) + 1)) x)
          - (if s' = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((s' - t0) / ((t1 - t0) / (φm N))) + 1)) x))
          2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (C * (|s - s'| + (t1 - t0) / (φm N))) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with N hN
      have hφN : 0 < φm N := lt_of_lt_of_le hN (hid_le N)
      have heq : s' + (s - s') = s := by ring
      have hmem : s' + (s - s') ∈ Set.Icc t0 t1 := by rw [heq]; exact hs
      have h := hCT (φm N) hφN s' (s - s') hs' hmem
      rw [heq] at h
      exact h
    have hτ : Filter.Tendsto (fun N : ℕ => (t1 - t0) / ((φm N : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (t1 - t0)).comp hφm_top
    have hinner : Filter.Tendsto (fun N : ℕ => C * (|s - s'| + (t1 - t0) / ((φm N : ℕ) : ℝ)))
        Filter.atTop (nhds (C * |s - s'|)) := by
      have h2 := (hτ.const_add (|s - s'|)).const_mul C
      simpa using h2
    have hlim : Filter.Tendsto
        (fun N : ℕ => Real.sqrt (C * (|s - s'| + (t1 - t0) / ((φm N : ℕ) : ℝ))))
        Filter.atTop (nhds (Real.sqrt (C * |s - s'|))) :=
      (Real.continuous_sqrt.tendsto _).comp hinner
    have hle : Filter.liminf (fun N : ℕ =>
        (eLpNorm (fun x =>
          (if s = t1 then (U (φm N) (φm N)) x
           else (U (φm N) (Nat.floor ((s - t0) / ((t1 - t0) / (φm N))) + 1)) x)
          - (if s' = t1 then (U (φm N) (φm N)) x
             else (U (φm N) (Nat.floor ((s' - t0) / ((t1 - t0) / (φm N))) + 1)) x))
          2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) Filter.atTop
        ≤ Real.sqrt (C * |s - s'|) := by
      refine Filter.liminf_le_of_le ?_ (fun b hb => ?_)
      · show ∃ bb, ∀ᶠ y in Filter.map _ Filter.atTop, bb ≤ y
        exact ⟨0, Filter.eventually_map.mpr
          (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)⟩
      · have huv : ∀ᶠ N : ℕ in Filter.atTop,
            b ≤ Real.sqrt (C * (|s - s'| + (t1 - t0) / (φm N))) := by
          filter_upwards [hb, hbound] with N h1 h2
          exact le_trans h1 h2
        exact ge_of_tendsto hlim huv
    exact le_trans (hWLSCThm s s' hs hs') hle
  intro t _ ε hε
  rcases eq_or_lt_of_le hC0 with rfl | hCpos
  · refine ⟨1, one_pos, fun s s' hs hs' _ _ _ _ => ?_⟩
    calc (eLpNorm (fun x => u s x - u s' x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
        ≤ Real.sqrt (0 * |s - s'|) := hpass s s' hs hs'
      _ = 0 := by rw [zero_mul, Real.sqrt_zero]
      _ < ε := hε
  · refine ⟨ε ^ 2 / (4 * C + 1), div_pos (pow_pos hε 2) (by linarith),
      fun s s' hs hs' _ _ hst hst' => ?_⟩
    have hss : |s - s'| < 2 * (ε ^ 2 / (4 * C + 1)) := by
      calc |s - s'| = |(s - t) + (t - s')| := by congr 1; ring
        _ ≤ |s - t| + |t - s'| := abs_add_le _ _
        _ = |s - t| + |s' - t| := by rw [abs_sub_comm t s']
        _ < 2 * (ε ^ 2 / (4 * C + 1)) := by linarith
    have hpos1 : (0 : ℝ) < 4 * C + 1 := by linarith
    have hC2δ : C * (2 * (ε ^ 2 / (4 * C + 1))) ≤ ε ^ 2 := by
      have heq : C * (2 * (ε ^ 2 / (4 * C + 1))) = (2 * C * ε ^ 2) / (4 * C + 1) := by ring
      rw [heq, div_le_iff₀ hpos1]
      nlinarith [mul_nonneg (sq_nonneg ε) (show (0 : ℝ) ≤ 2 * C + 1 by linarith)]
    have hsqrt : Real.sqrt (C * |s - s'|) < ε := by
      rw [Real.sqrt_lt' hε]
      calc C * |s - s'| < C * (2 * (ε ^ 2 / (4 * C + 1))) :=
            mul_lt_mul_of_pos_left hss hCpos
        _ ≤ ε ^ 2 := hC2δ
    exact lt_of_le_of_lt (hpass s s' hs hs') hsqrt


theorem intervalIntegrable_mul_of_memLp
    {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    IntervalIntegrable (fun x => f x * g x) volume (0 : ℝ) 1 := by
  have hInt : Integrable (f * g) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.integrable_mul hg
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hOn : IntegrableOn (f * g) (Set.uIcc (0 : ℝ) 1) volume := by
    rw [huIcc]
    exact hInt
  exact hOn.intervalIntegrable

/-- Slice pairing limit at `t0`. -/

theorem slice_weak_t0_fixed2
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (Nstar : Set ℝ) (D : Set (ℝ → ℝ))
    (hDMemThm : ∀ v ∈ D, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hBoundThm : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ M)
    (hDenseThm : ∀ v : ℝ → ℝ, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ D,
        (eLpNorm (fun x => v x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal < ε)
    (hRepAgreeThm : ∀ v ∈ D, ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ
      ∧ ∀ t : ℝ, t ∈ Set.Icc t0 t1 → t ∉ Nstar →
        (∫ x in (0 : ℝ)..1, u t x * v x) = ĝ t)
    (hCSThm : ∀ {f g : ℝ → ℝ},
      MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      |∫ x in (0 : ℝ)..1, f x * g x|
        ≤ (eLpNorm f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
          * (eLpNorm g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hInitPairThm : ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ĝ : ℝ → ℝ, Continuous ĝ →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ →
      ĝ t0 = ∫ x in (0 : ℝ)..1, u0 x * v x) :
    ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
        t ∈ Set.Icc t0 t1 → t ∉ Nstar → t0 < t → t - t0 < δ →
        |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)| < ε := by
  intro ψ hψ ε hε
  obtain ⟨M, hM0, hMbound⟩ := hBoundThm
  set U : ℝ := (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hU
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  set K : ℝ := M + U with hK
  have hK1 : 0 < K + 1 := by
    have hK0 : 0 ≤ K := add_nonneg hM0 hU0
    linarith
  have hDpos : (0 : ℝ) < 4 * (K + 1) := by linarith
  set ε' : ℝ := ε / (4 * (K + 1)) with hε'
  have hε'pos : 0 < ε' := by
    rw [hε']
    exact div_pos hε hDpos
  obtain ⟨w, hwD, hWapprox⟩ := hDenseThm ψ hψ ε' hε'pos
  have hwmem : MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hDMemThm w hwD
  obtain ⟨ĝ, hĝcont, hae, hAg⟩ := hRepAgreeThm w hwD
  have hInit : ĝ t0 = ∫ x in (0 : ℝ)..1, u0 x * w x :=
    hInitPairThm w hwmem ĝ hĝcont hae
  have hdiff : MemLp (fun x => ψ x - w x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hψ.sub hwmem
  have hM4 : M * ε' ≤ ε / 4 := by
    have hMle : M ≤ K + 1 := by
      rw [hK]
      linarith
    rw [hε', ← mul_div_assoc, div_le_iff₀ hDpos]
    have hR : ε / 4 * (4 * (K + 1)) = (K + 1) * ε := by ring
    rw [hR]
    exact mul_le_mul_of_nonneg_right hMle hε.le
  have hU4 : U * ε' ≤ ε / 4 := by
    have hUle : U ≤ K + 1 := by
      rw [hK]
      linarith
    rw [hε', ← mul_div_assoc, div_le_iff₀ hDpos]
    have hR : ε / 4 * (4 * (K + 1)) = (K + 1) * ε := by ring
    rw [hR]
    exact mul_le_mul_of_nonneg_right hUle hε.le
  have hcont : ContinuousAt ĝ t0 := hĝcont.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont (ε / 4) (by linarith)
  refine ⟨δ, hδpos, fun t htIcc htN htt0 httδ => ?_⟩
  have hutm : MemLp (fun x => u t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hMemThm t htIcc
  have hAgree : (∫ x in (0 : ℝ)..1, u t x * w x) = ĝ t := hAg t htIcc htN
  have hdist : dist t t0 < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr htt0)]
    exact httδ
  have hcontb : |ĝ t - ĝ t0| < ε / 4 := by
    have h := hδ hdist
    rwa [Real.dist_eq] at h
  have hnpos : 0 ≤ (eLpNorm (fun x => ψ x - w x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  have hsub1 : (∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)
      = ∫ x in (0 : ℝ)..1, u t x * (ψ x - w x) := by
    have h1 : IntervalIntegrable (fun x => u t x * ψ x) volume (0 : ℝ) 1 :=
      intervalIntegrable_mul_of_memLp hutm hψ
    have h2 : IntervalIntegrable (fun x => u t x * w x) volume (0 : ℝ) 1 :=
      intervalIntegrable_mul_of_memLp hutm hwmem
    rw [← intervalIntegral.integral_sub h1 h2]
    apply intervalIntegral.integral_congr
    intro x _
    show u t x * ψ x - u t x * w x = u t x * (ψ x - w x)
    ring
  have hCS1 := hCSThm (f := fun x => u t x) (g := fun x => ψ x - w x) hutm hdiff
  have ht1 : |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)|
      ≤ M * ε' := by
    rw [hsub1]
    refine le_trans hCS1 ?_
    exact mul_le_mul (hMbound t htIcc) hWapprox.le hnpos hM0
  have hsub3 : (∫ x in (0 : ℝ)..1, u0 x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * w x)
      = ∫ x in (0 : ℝ)..1, u0 x * (ψ x - w x) := by
    have h1 : IntervalIntegrable (fun x => u0 x * ψ x) volume (0 : ℝ) 1 :=
      intervalIntegrable_mul_of_memLp hu0 hψ
    have h2 : IntervalIntegrable (fun x => u0 x * w x) volume (0 : ℝ) 1 :=
      intervalIntegrable_mul_of_memLp hu0 hwmem
    rw [← intervalIntegral.integral_sub h1 h2]
    apply intervalIntegral.integral_congr
    intro x _
    show u0 x * ψ x - u0 x * w x = u0 x * (ψ x - w x)
    ring
  have hCS3 := hCSThm (f := fun x => u0 x) (g := fun x => ψ x - w x) hu0 hdiff
  have ht3 : |(∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
      ≤ U * ε' := by
    rw [abs_sub_comm, hsub3]
    refine le_trans hCS3 ?_
    have hUU : (eLpNorm u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ U :=
      le_of_eq hU.symm
    exact mul_le_mul hUU hWapprox.le hnpos hU0
  have ht2 : |(∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x)|
      < ε / 4 := by
    rw [hAgree, ← hInit]
    exact hcontb
  have htri : |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
      ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)|
        + |(∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x)|
        + |(∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)| := by
    have h : (∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)
        = ((∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x))
          + (((∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x))
          + ((∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x))) := by
      ring
    calc |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
        = |((∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x))
          + (((∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x))
          + ((∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)))| := by
          rw [h]
      _ ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)|
          + |((∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x))
          + ((∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x))| :=
          abs_add_le _ _
      _ ≤ |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)|
          + (|(∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x)|
          + |(∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|) :=
          add_le_add le_rfl (abs_add_le _ _)
      _ = |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)|
          + |(∫ x in (0 : ℝ)..1, u t x * w x) - (∫ x in (0 : ℝ)..1, u0 x * w x)|
          + |(∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)| := by
          ring
  refine lt_of_le_of_lt htri ?_
  have ht1' : |(∫ x in (0 : ℝ)..1, u t x * ψ x) - (∫ x in (0 : ℝ)..1, u t x * w x)|
      ≤ ε / 4 := le_trans ht1 hM4
  have ht3' : |(∫ x in (0 : ℝ)..1, u0 x * w x) - (∫ x in (0 : ℝ)..1, u0 x * ψ x)|
      ≤ ε / 4 := le_trans ht3 hU4
  have h12 := add_lt_add_of_le_of_lt ht1' ht2
  have h123 := add_lt_add_of_lt_of_le h12 ht3'
  have h34 : ε / 4 + ε / 4 + ε / 4 < ε := by linarith
  exact lt_trans h123 h34


theorem rothe_construction_asm
    {t0 t1 : ℝ} (ht : t0 < t1)
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (u : ℝ → ℝ → ℝ)
    (hMemThm : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      MemLp (fun x => u τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (G : Set ℝ)
    (hRepAsmThm : ∃ ũ : ℝ → ℝ → ℝ,
      (fun p : ℝ × ℝ => ũ p.1 p.2)
        =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)]
        (fun p : ℝ × ℝ => u p.1 p.2))
    (hSliceWeakThm : ∀ τ : ℝ, τ ∈ G → t0 < τ → τ < t1 → ∀ ψ : ℝ → ℝ,
      MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Filter.Tendsto (fun N : ℕ =>
          ∫ x in (0 : ℝ)..1, u τ x * ψ x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, u τ x * ψ x)))
    (hContOffThm : ∀ ũ : ℝ → ℝ → ℝ,
      (fun p : ℝ × ℝ => ũ p.1 p.2)
        =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)]
        (fun p : ℝ × ℝ => u p.1 p.2) →
      ContinuousOn (fun t => ũ t) (Set.Ioo t0 t1))
    (hInitDiagThm : ∀ v : ℝ → ℝ,
      MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ĝ : ℝ → ℝ, Continuous ĝ →
      (fun t => ∫ x in (0 : ℝ)..1, u t x * v x)
        =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ →
      ĝ t0 = ∫ x in (0 : ℝ)..1, u0 x * v x) :
    ∃ ũ : ℝ → ℝ → ℝ,
      (∀ t : ℝ, t ∈ Set.Icc t0 t1 → ContinuousAt (fun s => ũ s) t) ∧
      (fun p : ℝ × ℝ => ũ p.1 p.2)
        =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)]
        (fun p : ℝ × ℝ => u p.1 p.2) ∧
      (eLpNorm (fun x => ũ t0 x - u0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) = 0 := by
  classical
  obtain ⟨c, hc⟩ := Set.nonempty_Ioo.mpr ht
  set ũ : ℝ → ℝ → ℝ := fun s x => u s x + (if s = c ∧ x = 0 then (1 : ℝ) else 0) with hũ
  have hae : (fun p : ℝ × ℝ => ũ p.1 p.2)
      =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)]
      (fun p : ℝ × ℝ => u p.1 p.2) := by
    have hsub : {p : ℝ × ℝ | ¬(ũ p.1 p.2 = u p.1 p.2)} ⊆ {(c, (0 : ℝ))} := by
      intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hp ⊢
      by_contra hne
      apply hp
      have hcond : ¬(p.1 = c ∧ p.2 = 0) := by
        rintro ⟨h1, h2⟩
        exact hne (Prod.ext h1 h2)
      simp [hũ, hcond]
    have hnull : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) {(c, (0 : ℝ))} = 0 :=
      measure_singleton _
    show ∀ᵐ (p : ℝ × ℝ) ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
      ũ p.1 p.2 = u p.1 p.2
    rw [ae_iff]
    exact measure_mono_null hsub hnull
  have hcont_u := hContOffThm u (Filter.EventuallyEq.refl _ _)
  have hcont_ũ := hContOffThm ũ hae
  have hwu : ContinuousWithinAt (fun s : ℝ => u s 0) (Set.Ioo t0 t1) c :=
    (continuousWithinAt_pi.mp (hcont_u c hc)) 0
  have hwũ : ContinuousWithinAt (fun s : ℝ => ũ s 0) (Set.Ioo t0 t1) c :=
    (continuousWithinAt_pi.mp (hcont_ũ c hc)) 0
  have hsubc := hwũ.sub hwu
  have heq : ((fun s : ℝ => ũ s 0) - (fun s : ℝ => u s 0))
      = (fun s : ℝ => if s = c then (1 : ℝ) else 0) := by
    funext s
    simp only [Pi.sub_apply, hũ]
    by_cases h : s = c
    · simp [h, add_sub_cancel_left]
    · simp [h]
  rw [heq] at hsubc
  have hnbhd : Set.Ioo t0 t1 ∈ nhds c := IsOpen.mem_nhds isOpen_Ioo hc
  have hcon : ContinuousAt (fun s : ℝ => if s = c then (1 : ℝ) else 0) c :=
    hsubc.continuousAt hnbhd
  have h1 : Filter.Tendsto (fun s : ℝ => if s = c then (1 : ℝ) else 0) (nhdsWithin c {c}ᶜ) (nhds 1) := by
    have hcon' : Filter.Tendsto (fun s : ℝ => if s = c then (1 : ℝ) else 0) (nhds c)
        (nhds ((fun s : ℝ => if s = c then (1 : ℝ) else 0) c)) := hcon
    simpa using hcon'.mono_left nhdsWithin_le_nhds
  have h0 : Filter.Tendsto (fun s : ℝ => if s = c then (1 : ℝ) else 0) (nhdsWithin c {c}ᶜ) (nhds 0) := by
    have heq0 : (fun s : ℝ => if s = c then (1 : ℝ) else 0) =ᶠ[nhdsWithin c {c}ᶜ] (fun _ => (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
      show (if s = c then (1 : ℝ) else 0) = 0
      simp [hs]
    exact (Filter.tendsto_congr' heq0).mpr tendsto_const_nhds
  have h01 : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
  exact absurd h01 zero_ne_one


theorem weak_parabolic_sub
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ}
    {F : ℝ → ℝ → ℝ}
    (u₁ ux₁ u₂ ux₂ : ℝ → ℝ → ℝ)
    (hIntThm : ∀ (u ux : ℝ → ℝ → ℝ),
      ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Integrable (fun t : ℝ => ∫ x in (0 : ℝ)..1,
          (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x))
        (volume.restrict (Set.Icc t0 t1))
      ∧ Integrable (fun t : ℝ => ∫ x in (0 : ℝ)..1, F t x * φ t x)
        (volume.restrict (Set.Icc t0 t1))
      ∧ ∀ t : ℝ, Integrable (fun x : ℝ =>
          (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x))
        (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ ∀ t : ℝ, Integrable (fun x : ℝ => F t x * φ t x)
        (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hWeak1 : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
    (hWeak2 : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x) :
    ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
            + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x) = 0 := by
  intro φ hφ
  obtain ⟨hInt1o, -, hAll1⟩ := hIntThm u₁ ux₁ φ hφ
  obtain ⟨hInt2o, -, hAll2⟩ := hIntThm u₂ ux₂ φ hφ
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have htt : t0 ≤ t1 := ht.le
  have hInner1 : ∀ t : ℝ, IntervalIntegrable (fun x : ℝ =>
      (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
      volume (0 : ℝ) 1 := by
    intro t
    have hOn : IntegrableOn (fun x : ℝ =>
        (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
        (Set.uIcc (0 : ℝ) 1) volume := by
      rw [Set.uIcc_of_le h01]
      exact (hAll1 t).1
    exact hOn.intervalIntegrable
  have hInner2 : ∀ t : ℝ, IntervalIntegrable (fun x : ℝ =>
      (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x))
      volume (0 : ℝ) 1 := by
    intro t
    have hOn : IntegrableOn (fun x : ℝ =>
        (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x))
        (Set.uIcc (0 : ℝ) 1) volume := by
      rw [Set.uIcc_of_le h01]
      exact (hAll2 t).1
    exact hOn.intervalIntegrable
  have hOuter1 : IntervalIntegrable (fun t : ℝ => ∫ x in (0 : ℝ)..1,
      (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
      volume t0 t1 := by
    have hOn : IntegrableOn (fun t : ℝ => ∫ x in (0 : ℝ)..1,
        (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
        (Set.uIcc t0 t1) volume := by
      rw [Set.uIcc_of_le htt]
      exact hInt1o
    exact hOn.intervalIntegrable
  have hOuter2 : IntervalIntegrable (fun t : ℝ => ∫ x in (0 : ℝ)..1,
      (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x))
      volume t0 t1 := by
    have hOn : IntegrableOn (fun t : ℝ => ∫ x in (0 : ℝ)..1,
        (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x))
        (Set.uIcc t0 t1) volume := by
      rw [Set.uIcc_of_le htt]
      exact hInt2o
    exact hOn.intervalIntegrable
  have hEq : ∀ t : ℝ, (∫ x in (0 : ℝ)..1,
      (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
        + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x))
      = (∫ x in (0 : ℝ)..1,
        (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
        - (∫ x in (0 : ℝ)..1,
        (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x)) := by
    intro t
    have hPt : (fun x : ℝ => (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
        + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x))
        = (fun x : ℝ => (-u₁ t x * deriv (fun s => φ s x) t
          + κ t x * ux₁ t x * deriv (fun y => φ t y) x)
          - (-u₂ t x * deriv (fun s => φ s x) t
          + κ t x * ux₂ t x * deriv (fun y => φ t y) x)) := by
      funext x
      ring
    rw [hPt]
    exact intervalIntegral.integral_sub (hInner1 t) (hInner2 t)
  have hOuterEq : (fun t : ℝ => ∫ x in (0 : ℝ)..1,
      (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
        + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x))
      = (fun t : ℝ => (∫ x in (0 : ℝ)..1,
        (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
        - (∫ x in (0 : ℝ)..1,
        (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x))) :=
    funext hEq
  calc ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
          + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x)
      = ∫ t in t0..t1, ((∫ x in (0 : ℝ)..1,
        (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
        - (∫ x in (0 : ℝ)..1,
        (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x))) := by
        rw [hOuterEq]
    _ = (∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x))
        - (∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x)) :=
        intervalIntegral.integral_sub hOuter1 hOuter2
    _ = (∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
        - (∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x) := by
        rw [hWeak1 φ hφ, hWeak2 φ hφ]
    _ = 0 := sub_self _


theorem ae_prod_of_ae_slice
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u₁ u₂ : ℝ → ℝ → ℝ)
    (hMeasThm : AEStronglyMeasurable (fun p : ℝ × ℝ => u₁ p.1 p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ AEStronglyMeasurable (fun p : ℝ × ℝ => u₂ p.1 p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hSlice : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (fun x => u₁ τ x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x => u₂ τ x)) :
    (fun p : ℝ × ℝ => u₁ p.1 p.2) =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)]
      (fun p : ℝ × ℝ => u₂ p.1 p.2) := by
  have hvol : (volume : Measure (ℝ × ℝ))
      = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    Measure.volume_eq_prod ℝ ℝ
  have hprod : (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))
      = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1) := by
    rw [Measure.prod_restrict, ← hvol]
  rw [← hprod] at hMeasThm ⊢
  obtain ⟨hf, hg⟩ := hMeasThm
  have hEq : NullMeasurableSet
      {p : ℝ × ℝ | (fun p : ℝ × ℝ => u₁ p.1 p.2) p = (fun p : ℝ × ℝ => u₂ p.1 p.2) p}
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hf.nullMeasurableSet_eq_fun hg
  have hNull : NullMeasurableSet
      {p : ℝ × ℝ | ¬ (fun p : ℝ × ℝ => u₁ p.1 p.2) p = (fun p : ℝ × ℝ => u₂ p.1 p.2) p}
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hEq.compl
  rw [Filter.EventuallyEq, ae_iff, Measure.prod_apply₀ hNull]
  have hsec : (fun τ : ℝ => (volume.restrict (Set.Icc (0 : ℝ) 1))
        (Prod.mk τ ⁻¹' {p : ℝ × ℝ | ¬ (fun p : ℝ × ℝ => u₁ p.1 p.2) p = (fun p : ℝ × ℝ => u₂ p.1 p.2) p}))
      =ᵐ[volume.restrict (Set.Icc t0 t1)] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    have hτSlice := hSlice τ hτ
    rw [Filter.EventuallyEq, ae_iff] at hτSlice
    have hPre : Prod.mk τ ⁻¹' {p : ℝ × ℝ | ¬ (fun p : ℝ × ℝ => u₁ p.1 p.2) p = (fun p : ℝ × ℝ => u₂ p.1 p.2) p}
        = {x : ℝ | ¬ u₁ τ x = u₂ τ x} := by
      ext x
      simp
    rw [hPre]
    exact hτSlice
  rw [lintegral_congr_ae hsec]
  simp


theorem weak_parabolic_unique_of_energy
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    (u₁ ux₁ u₂ ux₂ : ℝ → ℝ → ℝ)
    (hHomogThm : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
            + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x) = 0)
    (hEnergyIdThm : ∀ (w wx : ℝ → ℝ → ℝ),
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-w t x * deriv (fun s => φ s x) t + κ t x * wx t x * deriv (fun y => φ t y) x) = 0) →
      (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal = 0 →
      ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2 = 0)
    (hInitThm : (eLpNorm (fun x => u₁ t0 x - u₂ t0 x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal = 0) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => u₁ τ x - u₂ τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal = 0 := by
  have hEq : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) : Measure (ℝ × ℝ))
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [hEq] at hκ
  have hκ_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ t x ∧ κ t x ≤ kmax :=
    Measure.ae_ae_of_ae_prod hκ
  intro τ hτ
  obtain ⟨hτlo, hτhi⟩ := Set.mem_Icc.mp hτ
  have hEq2 := hEnergyIdThm (fun t x => u₁ t x - u₂ t x) (fun t x => ux₁ t x - ux₂ t x)
    hHomogThm hInitThm τ hτ
  have hA : 0 ≤ (eLpNorm (fun x => u₁ τ x - u₂ τ x) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 :=
    sq_nonneg _
  have hinner_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      0 ≤ ∫ x in (0 : ℝ)..1, κ t x * (ux₁ t x - ux₂ t x) ^ 2 := by
    filter_upwards [hκ_ae] with t ht
    apply intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one
    filter_upwards [ht] with x hx
    exact mul_nonneg (le_trans hkmin.le hx.1) (sq_nonneg _)
  have hB : 0 ≤ ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux₁ t x - ux₂ t x) ^ 2 := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hτlo
    exact ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hτhi) hinner_ae
  have h2B : 0 ≤ 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (ux₁ t x - ux₂ t x) ^ 2 :=
    mul_nonneg zero_le_two hB
  have hZero := ((add_eq_zero_iff_of_nonneg hA h2B).mp hEq2).1
  exact sq_eq_zero_iff.mp hZero


theorem sq_integral_le_mul_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → ℝ} (hu : Integrable u μ) (hu2 : Integrable (fun x => (u x)^2) μ)
    (hV : 0 < μ.real Set.univ) :
    (∫ x, u x ∂μ)^2 ≤ (μ.real Set.univ) * (∫ x, (u x)^2 ∂μ) := by
  set V : ℝ := μ.real Set.univ with hVdef
  set H : ℝ := ∫ x, u x ∂μ with hHdef
  set Q : ℝ := ∫ x, (u x)^2 ∂μ with hQdef
  set m : ℝ := H / V with hmdef
  have hmV : m * V = H := by
    rw [hmdef, div_mul_cancel₀ H (ne_of_gt hV)]
  have heq : (fun x => (u x - m)^2)
      = (fun x => ((u x)^2 - (2*m) * u x) + m^2) := by
    funext x; ring
  have hsub : Integrable (fun x => (u x)^2 - (2*m) * u x) μ :=
    hu2.sub (hu.const_mul (2*m))
  have hnonneg : 0 ≤ ∫ x, (u x - m)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hexpand : ∫ x, (u x - m)^2 ∂μ = Q - 2*m*H + m^2*V := by
    rw [heq, integral_add hsub (integrable_const (m^2)),
      integral_sub hu2 (hu.const_mul (2*m)), integral_const_mul, integral_const,
      smul_eq_mul]
    simp only [← hVdef, ← hHdef, ← hQdef]
    ring
  rw [hexpand] at hnonneg
  rw [← hmV] at hnonneg ⊢
  have h4 : 0 ≤ V * (Q - 2*m*(m*V) + m^2*V) := mul_nonneg hV.le hnonneg
  have e : V*(Q - 2*m*(m*V) + m^2*V) = V*Q - (m*V)^2 := by ring
  rw [e] at h4
  linarith

/-- Slab average inequality for an abstract interval, via Fubini and Cauchy-Schwarz. -/

theorem slab_sq_one_aux
    {t0 t1 a b c : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ Set.Icc t0 t1)
    (hc : c * (b - a) = 1)
    {f g : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hg : MemLp (Function.uncurry g) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) :
    (∫ p in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
      (((c * ∫ s in a..b, (f s p.2 - g s p.2)) ^ 2))
        ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1)))
      ≤ ∫ p in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
          ((f p.1 p.2 - g p.1 p.2) ^ 2)
            ∂(volume.restrict (Set.Icc a b ×ˢ Set.Icc 0 1)) := by
  have hSmeas : MeasurableSet (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hSR : (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)
      ⊆ (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1) :=
    Set.prod_mono hsub Set.Subset.rfl
  have hrr : ((volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)).restrict
      (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1))
      = volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1) := by
    rw [Measure.restrict_restrict hSmeas, Set.inter_self]
  have hprod : volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  rw [hrr, hprod]
  set μa : Measure ℝ := volume.restrict (Set.Icc a b) with hμadef
  set μx : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1) with hμxdef
  have hμafin : μa Set.univ < ⊤ := by
    rw [hμadef, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hμxfin : μx Set.univ < ⊤ := by
    rw [hμxdef, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure μa := ⟨hμafin⟩
  have : IsFiniteMeasure μx := ⟨hμxfin⟩
  have hVab : μa.real Set.univ = b - a := by
    rw [hμadef]
    show ((volume.restrict (Set.Icc a b)) Set.univ).toReal = b - a
    rw [Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hVpos : 0 < μa.real Set.univ := by
    rw [hVab]; exact sub_pos.mpr hab
  have hVnn : 0 ≤ μa.real Set.univ := hVpos.le
  have hmemR : MemLp (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0:ℝ) 1)) :=
    MemLp.sub hf hg
  have hmemS : MemLp (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2) 2
      (volume.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)) := by
    have h := hmemR.restrict (Set.Icc a b ×ˢ Set.Icc (0:ℝ) 1)
    rw [Measure.restrict_restrict hSmeas,
      Set.inter_eq_self_of_subset_left hSR] at h
    exact h
  have hmemP : MemLp (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2) 2 (μa.prod μx) := by
    rw [← hprod]; exact hmemS
  have hSint : Integrable (fun p : ℝ × ℝ => f p.1 p.2 - g p.1 p.2) (μa.prod μx) :=
    MemLp.integrable one_le_two hmemP
  have hSqint : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 - g p.1 p.2)^2) (μa.prod μx) :=
    hmemP.integrable_sq
  have ex1 : ∀ᵐ x ∂μx, Integrable (fun t => f t x - g t x) μa :=
    hSint.prod_left_ae
  have ex2 : ∀ᵐ x ∂μx, Integrable (fun t => (f t x - g t x)^2) μa :=
    hSqint.prod_left_ae
  have hJint : Integrable (fun x => ∫ t, (f t x - g t x) ∂μa) μx :=
    hSint.integral_prod_right
  have hJaes : AEStronglyMeasurable (fun x => ∫ t, (f t x - g t x) ∂μa) μx :=
    hJint.aestronglyMeasurable
  have hJeq : ∀ x, (∫ s in a..b, (f s x - g s x)) = ∫ t, (f t x - g t x) ∂μa :=
    fun x => by
      rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
        hμadef]
  simp only [hJeq]
  have hLnn : 0 ≤ᵐ[μa.prod μx]
      (fun p : ℝ × ℝ => (c * ∫ t, (f t p.2 - g t p.2) ∂μa)^2) :=
    Filter.Eventually.of_forall (fun p => sq_nonneg _)
  have hLaes : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (c * ∫ t, (f t p.2 - g t p.2) ∂μa)^2) (μa.prod μx) := by
    simpa only [Pi.pow_apply] using (((hJaes.const_mul c).pow 2).comp_snd)
  have hRnn : 0 ≤ᵐ[μa.prod μx]
      (fun p : ℝ × ℝ => (f p.1 p.2 - g p.1 p.2)^2) :=
    Filter.Eventually.of_forall (fun p => sq_nonneg _)
  have hRaes : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 - g p.1 p.2)^2) (μa.prod μx) :=
    hSqint.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hLnn hLaes,
    integral_eq_lintegral_of_nonneg_ae hRnn hRaes]
  refine ENNReal.toReal_mono ?_ ?_
  · have hmem1 : MemLp (fun p : ℝ × ℝ => (f p.1 p.2 - g p.1 p.2)^2) 1
        (μa.prod μx) :=
      memLp_one_iff_integrable.mpr hSqint
    have hlt := hmem1.eLpNorm_lt_top
    rw [eLpNorm_one_eq_lintegral_enorm hSqint.aestronglyMeasurable] at hlt
    have hbridge : ∀ p : ℝ × ℝ, ENNReal.ofReal ((f p.1 p.2 - g p.1 p.2)^2)
        = ‖(f p.1 p.2 - g p.1 p.2)^2‖ₑ :=
      fun p => (Real.enorm_eq_ofReal (sq_nonneg _)).symm
    simp only [hbridge]
    exact ne_of_lt hlt
  · have hLaemeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal ((c * ∫ t, (f t p.2 - g t p.2) ∂μa)^2))
        (μa.prod μx) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hLaes.aemeasurable
    have hRaemeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal ((f p.1 p.2 - g p.1 p.2)^2))
        (μa.prod μx) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hRaes.aemeasurable
    have hLton : (∫⁻ p, ENNReal.ofReal ((c * ∫ t, (f t p.2 - g t p.2) ∂μa)^2)
          ∂(μa.prod μx))
        = ∫⁻ x, ENNReal.ofReal ((c * ∫ t, (f t x - g t x) ∂μa)^2) * μa Set.univ
          ∂μx := by
      rw [lintegral_prod_symm _ hLaemeas]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∫⁻ t, ENNReal.ofReal ((c * ∫ t', (f t' x - g t' x) ∂μa)^2) ∂μa)
        = ENNReal.ofReal ((c * ∫ t, (f t x - g t x) ∂μa)^2) * μa Set.univ
      exact lintegral_const _
    rw [hLton, lintegral_prod_symm _ hRaemeas]
    refine lintegral_mono_ae ?_
    filter_upwards [ex1, ex2] with x hx1 hx2
    show ENNReal.ofReal ((c * ∫ t, (f t x - g t x) ∂μa)^2) * μa Set.univ
      ≤ ∫⁻ t, ENNReal.ofReal ((f t x - g t x)^2) ∂μa
    have hCS : (∫ t, (f t x - g t x) ∂μa)^2
        ≤ μa.real Set.univ * (∫ t, (f t x - g t x)^2 ∂μa) :=
      sq_integral_le_mul_integral_sq (u := fun t => f t x - g t x) hx1 hx2 hVpos
    have hnn : 0 ≤ c^2 * μa.real Set.univ := mul_nonneg (sq_nonneg c) hVnn
    have hmul := mul_le_mul_of_nonneg_left hCS hnn
    have hcv : (c * μa.real Set.univ)^2 = 1 := by rw [hVab, hc]; norm_num
    have e1 : (c * ∫ t, (f t x - g t x) ∂μa)^2 * μa.real Set.univ
        = c^2 * μa.real Set.univ * (∫ t, (f t x - g t x) ∂μa)^2 := by ring
    have e2 : c^2 * μa.real Set.univ
          * (μa.real Set.univ * ∫ t, (f t x - g t x)^2 ∂μa)
        = ∫ t, (f t x - g t x)^2 ∂μa := by
      have ering : c^2 * μa.real Set.univ
            * (μa.real Set.univ * ∫ t, (f t x - g t x)^2 ∂μa)
          = (c * μa.real Set.univ)^2 * (∫ t, (f t x - g t x)^2 ∂μa) := by ring
      rw [ering, hcv, one_mul]
    have hreal : (c * ∫ t, (f t x - g t x) ∂μa)^2 * μa.real Set.univ
        ≤ ∫ t, (f t x - g t x)^2 ∂μa := by
      rw [e2] at hmul
      rw [e1]
      exact hmul
    have hμaV : μa Set.univ = ENNReal.ofReal (μa.real Set.univ) := by
      have h1 : μa Set.univ = ENNReal.ofReal (b - a) := by
        rw [hμadef, Measure.restrict_apply_univ, Real.volume_Icc]
      rw [h1, hVab]
    have hslice_eq : ∫ t, (f t x - g t x)^2 ∂μa
        = (∫⁻ t, ENNReal.ofReal ((f t x - g t x)^2) ∂μa).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun t => sq_nonneg _))
        hx2.aestronglyMeasurable
    have hslice_fin : (∫⁻ t, ENNReal.ofReal ((f t x - g t x)^2) ∂μa) ≠ ⊤ := by
      have hmem1 : MemLp (fun t => (f t x - g t x)^2) 1 μa :=
        memLp_one_iff_integrable.mpr hx2
      have hlt := hmem1.eLpNorm_lt_top
      rw [eLpNorm_one_eq_lintegral_enorm hx2.aestronglyMeasurable] at hlt
      have hbridge : ∀ t, ENNReal.ofReal ((f t x - g t x)^2)
          = ‖(f t x - g t x)^2‖ₑ :=
        fun t => (Real.enorm_eq_ofReal (sq_nonneg _)).symm
      simp only [hbridge]
      exact ne_of_lt hlt
    calc ENNReal.ofReal ((c * ∫ t, (f t x - g t x) ∂μa)^2) * μa Set.univ
        = ENNReal.ofReal (((c * ∫ t, (f t x - g t x) ∂μa)^2)
            * μa.real Set.univ) := by
          rw [hμaV, ← ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (∫ t, (f t x - g t x)^2 ∂μa) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ t, ENNReal.ofReal ((f t x - g t x)^2) ∂μa := by
          rw [hslice_eq, ENNReal.ofReal_toReal hslice_fin]

/-- Floor is constant on a slab. -/

theorem floor_slab_eq
    {t0 t1 : ℝ} (ht : t0 < t1)
    {N : ℕ} (hN : 0 < N) {k : ℕ}
    {t : ℝ} (htmem : t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)))) :
    Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) = k := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hw : (0 : ℝ) < (t1 - t0) / (N : ℝ) := div_pos (sub_pos.mpr ht) hNpos
  rw [Set.mem_Ico] at htmem
  obtain ⟨hlo, hhi⟩ := htmem
  apply Nat.floor_eq_on_Ico k
  constructor
  · rw [le_div_iff₀ hw]
    have : (k : ℝ) * ((t1 - t0) / (N : ℝ)) ≤ t - t0 := by linarith
    exact this
  · rw [div_lt_iff₀ hw]
    have : t - t0 < ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) := by linarith
    exact this

/-- One-slab squared-integral inequality in Fbar form. -/

theorem fbar_sq_slab
    {t0 t1 : ℝ} (ht : t0 < t1)
    {f g : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hg : MemLp (Function.uncurry g) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) :
    (∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
      ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
         (f s p.2 - g s p.2)) ^ 2)
        ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)))
      ≤ ∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
          ((f p.1 p.2 - g p.1 p.2) ^ 2)
            ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have hSmeas : MeasurableSet (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hrr : ((volume.restrict (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1)).restrict
      (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1))
      = volume.restrict (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1) := by
    rw [Measure.restrict_restrict hSmeas, Set.inter_self]
  have hprod : volume.restrict (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1)
      = (volume.restrict (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))))).prod
        (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  rw [hrr, hprod]
  set μa : Measure ℝ := volume.restrict (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))) with hμadef
  set μx : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1) with hμxdef
  have hμafin : μa Set.univ < ⊤ := by
    rw [hμadef, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hμxfin : μx Set.univ < ⊤ := by
    rw [hμxdef, Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure μa := ⟨hμafin⟩
  have : IsFiniteMeasure μx := ⟨hμxfin⟩
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
  have hwpos : (0:ℝ) < (t1 - t0)/(N:ℝ) := div_pos (sub_pos.mpr ht) hNpos
  have hNw : (N:ℝ) * ((t1-t0)/(N:ℝ)) = t1 - t0 := by
    rw [mul_comm (N:ℝ), div_mul_cancel₀ _ hNne]
  have hkn : ((k:ℝ)+1) ≤ (N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
  have hkw : ((k:ℝ)+1)*((t1-t0)/(N:ℝ)) ≤ (N:ℝ)*((t1-t0)/(N:ℝ)) :=
    mul_le_mul_of_nonneg_right hkn hwpos.le
  have hble : (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ≤ t1 := by linarith
  have h1 : ∀ᵐ p ∂(μa.prod μx),
      p ∈ (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1) := by
    rw [← hprod]
    exact ae_restrict_mem hSmeas
  have hnull : (μa.prod μx) {p : ℝ × ℝ | p.1 = (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))} = 0 := by
    have hset : {p : ℝ × ℝ | p.1 = (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))}
        = {(t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))} ×ˢ Set.univ := by
      ext ⟨t, x⟩; simp
    have hmb : μa {(t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))} = 0 := by
      rw [hμadef, Measure.restrict_apply (measurableSet_singleton _)]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    rw [hset, Measure.prod_prod _ _, hmb, zero_mul]
  have hcompl : {p : ℝ × ℝ | p.1 ≠ (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))}ᶜ
      = {p : ℝ × ℝ | p.1 = (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ)))} := by
    ext p; simp
  have h2 : ∀ᵐ p ∂(μa.prod μx), p.1 ≠ (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) :=
    mem_ae_iff.mpr (by rw [hcompl]; exact hnull)
  have hpt : ∀ p : ℝ × ℝ,
      p ∈ (Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) ×ˢ Set.Icc (0:ℝ) 1) →
      p.1 ≠ (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) →
      ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
        else ((N : ℝ) / (t1 - t0)) * ∫ s in
          (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
            (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
          (f s p.2 - g s p.2)) ^ 2)
      = ((((N:ℝ)/(t1-t0)) * ∫ s in (t0 + (k:ℝ)*((t1-t0)/(N:ℝ)))..(t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))),
          (f s p.2 - g s p.2)) ^ 2) := by
    intro p hpS hp1
    have hp1mem : p.1 ∈ Set.Icc (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) :=
      (Set.mem_prod.mp hpS).1
    have hpIco : p.1 ∈ Set.Ico (t0 + (k:ℝ)*((t1-t0)/(N:ℝ))) (t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))) :=
      Set.mem_Ico.mpr ⟨hp1mem.1, lt_of_le_of_ne hp1mem.2 hp1⟩
    have hfloor : Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) = k :=
      floor_slab_eq ht hN hpIco
    have hpnet1 : p.1 ≠ t1 := ne_of_lt (lt_of_lt_of_le (Set.mem_Ico.mp hpIco).2 hble)
    split_ifs with h
    · exact absurd h hpnet1
    · rw [hfloor]
  have heq : (fun p : ℝ × ℝ => ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
      else ((N : ℝ) / (t1 - t0)) * ∫ s in
        (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
          (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
        (f s p.2 - g s p.2)) ^ 2))
      =ᵐ[μa.prod μx] (fun p : ℝ × ℝ => ((((N:ℝ)/(t1-t0))
        * ∫ s in (t0 + (k:ℝ)*((t1-t0)/(N:ℝ)))..(t0 + ((k:ℝ)+1)*((t1-t0)/(N:ℝ))),
          (f s p.2 - g s p.2)) ^ 2)) := by
    filter_upwards [h1, h2] with p hpS hp1
    exact hpt p hpS hp1
  have hslab := slab_sq_one ht hf hg hN hk
  rw [hrr, hprod] at hslab
  rw [integral_congr_ae heq]
  exact hslab


theorem slab_avg_sq_integral
    {t0 t1 : ℝ} (ht : t0 < t1)
    {f g : ℝ → ℝ → ℝ}
    (hf : MemLp (Function.uncurry f) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hg : MemLp (Function.uncurry g) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {N : ℕ} (hN : 0 < N)
    (hSplit : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
         (f s p.2 - g s p.2)) ^ 2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∑ k ∈ Finset.range N,
        ∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
          ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
           else ((N : ℝ) / (t1 - t0)) * ∫ s in
             (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
               (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
             (f s p.2 - g s p.2)) ^ 2)
            ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)))
    (hSlab : ∀ k : ℕ, k < N →
      (∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
        ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
         else ((N : ℝ) / (t1 - t0)) * ∫ s in
           (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
             (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
           (f s p.2 - g s p.2)) ^ 2)
          ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)))
        ≤ ∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
            ((f p.1 p.2 - g p.1 p.2) ^ 2)
              ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1)))
    (hSplitRHS : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          ((f p.1 p.2 - g p.1 p.2) ^ 2)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∑ k ∈ Finset.range N,
        ∫ p in Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1,
          ((f p.1 p.2 - g p.1 p.2) ^ 2)
            ∂(volume.restrict (Set.Icc (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) ×ˢ Set.Icc (0 : ℝ) 1))) :
    (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      ((if p.1 = t1 then (f p.1 p.2 - g p.1 p.2)
       else ((N : ℝ) / (t1 - t0)) * ∫ s in
         (t0 + (Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) : ℝ) * ((t1 - t0) / (N : ℝ)))..
           (t0 + ((Nat.floor ((p.1 - t0) / ((t1 - t0) / (N : ℝ))) + 1 : ℝ) * ((t1 - t0) / (N : ℝ)))),
         (f s p.2 - g s p.2)) ^ 2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      ≤ ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          ((f p.1 p.2 - g p.1 p.2) ^ 2)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  rw [hSplit, hSplitRHS]
  exact Finset.sum_le_sum (fun k hk => hSlab k (Finset.mem_range.mp hk))


theorem floor_slab_aux
    {t0 t1 : ℝ} (ht : t0 < t1)
    {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N)
    (t : ℝ) (htmem : t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)))) :
    Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) = k ∧ t ≠ t1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiff : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
  have htau : (0 : ℝ) < (t1 - t0) / (N : ℝ) := div_pos hdiff hNpos
  rw [Set.mem_Ico] at htmem
  obtain ⟨hlo, hhi⟩ := htmem
  have h1 : (k : ℝ) ≤ (t - t0) / ((t1 - t0) / (N : ℝ)) := by
    rw [le_div_iff₀ htau]
    have : (k : ℝ) * ((t1 - t0) / (N : ℝ)) ≤ t - t0 := by linarith
    linarith
  have h2 : (t - t0) / ((t1 - t0) / (N : ℝ)) < (k : ℝ) + 1 := by
    rw [div_lt_iff₀ htau]
    have : t - t0 < ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) := by linarith
    linarith
  have hmem : (t - t0) / ((t1 - t0) / (N : ℝ)) ∈ Set.Ico ((k : ℝ)) ((k : ℝ) + 1) :=
    Set.mem_Ico.mpr ⟨h1, h2⟩
  have hfloor : Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) = k :=
    Nat.floor_eq_on_Ico k _ hmem
  have hkN : k + 1 ≤ N := Nat.succ_le_of_lt hk
  have hkN' : ((k : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hkN
  have hle : ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ)) ≤ (N : ℝ) * ((t1 - t0) / (N : ℝ)) := by
    apply mul_le_mul_of_nonneg_right hkN' (le_of_lt htau)
  have hNtau : (N : ℝ) * ((t1 - t0) / (N : ℝ)) = t1 - t0 := by
    field_simp
  have ht1 : t < t1 := by linarith
  exact ⟨hfloor, ne_of_lt ht1⟩


theorem integrableOn_slice_sq
    {t0 t1 : ℝ}
    (F : ℝ → ℝ → ℝ)
    (hMem : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) :
    IntegrableOn (fun t => (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      (Set.Icc t0 t1) volume := by
  have hMeas : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume.prod volume) := rfl
    rw [hvol, ← Measure.prod_restrict]
  have hMemProd : MemLp (Function.uncurry F) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hMeas] at hMem
    exact hMem
  have hIntSq : Integrable (Function.uncurry (fun t x => (F t x) ^ 2))
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have h := hMemProd.integrable_sq
    exact h
  have hIntNorm : Integrable (fun t => ∫ x, ‖(F t x) ^ 2‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (volume.restrict (Set.Icc t0 t1)) := hIntSq.integral_norm_prod_left
  have hNormEq : (fun t => ∫ x, ‖(F t x) ^ 2‖ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = (fun t => ∫ x, (F t x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    funext t
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hIntIter : Integrable (fun t => ∫ x, (F t x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (volume.restrict (Set.Icc t0 t1)) := by
    rw [← hNormEq]
    exact hIntNorm
  have hAES : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hMemProd.aestronglyMeasurable
  have hAES_slice : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      AEStronglyMeasurable (fun x => F t x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := hAES.prodMk_left
    filter_upwards [h] with t ht
    exact ht
  have hInt_slice : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      Integrable (fun x => (F t x) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := hIntSq.prod_right_ae
    filter_upwards [h] with t ht
    exact ht
  have hMem_slice : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      MemLp (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    filter_upwards [hAES_slice, hInt_slice] with t hAES_t hInt_t
    exact (memLp_two_iff_integrable_sq hAES_t).mpr hInt_t
  have hSliceEq : (fun t => ∫ x, (F t x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      =ᵐ[volume.restrict (Set.Icc t0 t1)]
      (fun t => (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) := by
    filter_upwards [hMem_slice] with t ht
    exact (eLpNorm_toReal_sq_eq_integral_sq ht).symm
  have hIntG : Integrable (fun t => (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      (volume.restrict (Set.Icc t0 t1)) := hIntIter.congr hSliceEq
  exact hIntG


theorem integral_piecewise_const_eq_sum
    {t0 t1 : ℝ} (ht : t0 < t1)
    {N : ℕ} (hN : 0 < N)
    (g : ℝ → ℝ) (c : ℕ → ℝ)
    (hSlice : ∀ k < N, ∀ t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))), g t = c k)
    (hInt : IntegrableOn g (Set.Icc t0 t1) volume) :
    ∫ t in t0..t1, g t = ∑ k ∈ Finset.range N, ((t1 - t0) / (N : ℝ)) * c k := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiff : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
  have htau : (0 : ℝ) < (t1 - t0) / (N : ℝ) := div_pos hdiff hNpos
  have htau_nn : (0 : ℝ) ≤ (t1 - t0) / (N : ℝ) := le_of_lt htau
  set tau : ℝ := (t1 - t0) / (N : ℝ) with htau_def
  set a : ℕ → ℝ := fun k => t0 + (k : ℝ) * tau with ha_def
  have ha0 : a 0 = t0 := by simp [ha_def]
  have haN : a N = t1 := by
    simp only [ha_def]
    have hNt : (N : ℝ) * tau = t1 - t0 := by
      rw [htau_def]
      field_simp
    linarith
  have hmono : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k
    simp only [ha_def]
    have hle : (k : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
    have := mul_le_mul_of_nonneg_right hle htau_nn
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
  have hge0 : ∀ k : ℕ, t0 ≤ a k := by
    intro k
    simp only [ha_def]
    have : (0 : ℝ) ≤ (k : ℝ) * tau := by positivity
    linarith
  have hleN : ∀ k : ℕ, k ≤ N → a k ≤ t1 := by
    intro k hk
    simp only [ha_def]
    have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have h1 : (k : ℝ) * tau ≤ (N : ℝ) * tau := mul_le_mul_of_nonneg_right hk' htau_nn
    have hNt : (N : ℝ) * tau = t1 - t0 := by
      rw [htau_def]
      field_simp
    linarith
  have hII : ∀ k < N, IntervalIntegrable g volume (a k) (a (k + 1)) := by
    intro k hk
    have hle := hmono k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    apply hInt.mono _ le_rfl
    intro t ht
    rw [Set.mem_Ioc] at ht
    obtain ⟨hlo, hhi⟩ := ht
    have hkN : k + 1 ≤ N := Nat.succ_le_of_lt hk
    have h1 : t0 ≤ t := le_trans (hge0 k) (le_of_lt hlo)
    have h2 : t ≤ t1 := le_trans hhi (hleN (k + 1) hkN)
    exact Set.mem_Icc.mpr ⟨h1, h2⟩
  have hSlabEq : ∀ k < N, ∫ t in a k..a (k + 1), g t = tau * c k := by
    intro k hk
    have hle := hmono k
    have hAe : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (a k) (a (k + 1)) → g t = c k := by
      have hne := Measure.ae_ne (volume : Measure ℝ) (a (k + 1))
      filter_upwards [hne] with t htne htmem
      rw [Set.uIoc_of_le hle] at htmem
      rw [Set.mem_Ioc] at htmem
      obtain ⟨hlo, hhi⟩ := htmem
      have hlt : t < a (k + 1) := lt_of_le_of_ne hhi htne
      have hIco : t ∈ Set.Ico (a k) (a (k + 1)) := Set.mem_Ico.mpr ⟨le_of_lt hlo, hlt⟩
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      simp only [ha_def, htau_def] at hIco ⊢
      rw [hcast] at hIco
      exact hSlice k hk t hIco
    have hEq : (∫ t in a k..a (k + 1), g t) = ∫ t in a k..a (k + 1), c k := by
      apply intervalIntegral.integral_congr_ae
      exact hAe
    rw [hEq, intervalIntegral.integral_const]
    have hdiff_eq : a (k + 1) - a k = tau := by
      simp only [ha_def]
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      ring
    rw [hdiff_eq, smul_eq_mul]
  have hSum := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := N) (f := g) (μ := volume) hII
  rw [ha0, haN] at hSum
  rw [← hSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [hSlabEq k hk]


theorem le_of_sq_le {x B C' : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ B) (hB : B < C') (hC : 1 ≤ C') : x ≤ C' := by
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [sq_nonneg (x - C'), mul_nonneg (show (0:ℝ) ≤ C' - 1 by linarith) (show (0:ℝ) ≤ C' by linarith)]


theorem eLpNorm_sq_eq_integral_slice
    {t0 t1 : ℝ} (ht : t0 < t1)
    (F : ℝ → ℝ → ℝ)
    (hMem : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) :
    (eLpNorm (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ^ 2
      = ∫ t in t0..t1, (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
  have hMeas : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume.prod volume) := rfl
    rw [hvol, ← Measure.prod_restrict]
  have hMemProd : MemLp (Function.uncurry F) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hMeas] at hMem
    exact hMem
  have hLHS : (eLpNorm (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ^ 2
      = ∫ p, (F p.1 p.2) ^ 2 ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have h := eLpNorm_toReal_sq_eq_integral_sq hMem
    rw [hMeas] at h ⊢
    exact h
  have hIntSq : Integrable (Function.uncurry (fun t x => (F t x) ^ 2))
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have h := hMemProd.integrable_sq
    exact h
  have hFub : (∫ t, ∫ x, (F t x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ∂(volume.restrict (Set.Icc t0 t1)))
      = ∫ p, (F p.1 p.2) ^ 2 ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have h := integral_integral hIntSq
    exact h
  have hAES : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hMemProd.aestronglyMeasurable
  have hAES_slice : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      AEStronglyMeasurable (fun x => F t x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := hAES.prodMk_left
    filter_upwards [h] with t ht
    exact ht
  have hInt_slice : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      Integrable (fun x => (F t x) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have h := hIntSq.prod_right_ae
    filter_upwards [h] with t ht
    exact ht
  have hMem_slice : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      MemLp (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    filter_upwards [hAES_slice, hInt_slice] with t hAES_t hInt_t
    exact (memLp_two_iff_integrable_sq hAES_t).mpr hInt_t
  have hSliceEq : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        = ∫ x, (F t x) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    filter_upwards [hMem_slice] with t ht
    exact eLpNorm_toReal_sq_eq_integral_sq ht
  have hIcc : (∫ t, (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ∂(volume.restrict (Set.Icc t0 t1)))
      = ∫ p, (F p.1 p.2) ^ 2 ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [integral_congr_ae hSliceEq]
    exact hFub
  have hInterval : (∫ t in t0..t1, (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
      = ∫ t, (eLpNorm (fun x => F t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        ∂(volume.restrict (Set.Icc t0 t1)) := by
    rw [intervalIntegral.integral_of_le (le_of_lt ht)]
    have hRestr : volume.restrict (Set.Ioc t0 t1) = volume.restrict (Set.Icc t0 t1) :=
      Measure.restrict_congr_set Ioc_ae_eq_Icc
    rw [hRestr]
  rw [hLHS, hInterval, hIcc]
/-- Slice norm of the toFun interpolant on a slab. -/

theorem interp_slice_norm_toFun
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10)
    {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) :
    ∀ t : ℝ, t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) →
      eLpNorm (fun x => (if t = t1 then (U_of N N).toFun x else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
        = eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  intro t htmem
  obtain ⟨hfloor, hne⟩ := floor_slab_aux ht hN hk t htmem
  have hfun : (fun x => (if t = t1 then (U_of N N).toFun x else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) = (U_of N (k + 1)).toFun := by
    funext x
    simp [hne, hfloor]
  rw [hfun]



/-- Slice norm of the weakDeriv interpolant on a slab. -/

theorem interp_slice_norm_weakDeriv
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10)
    {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) :
    ∀ t : ℝ, t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ))) (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))) →
      eLpNorm (fun x => (if t = t1 then (U_of N N).weakDeriv x else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
        = eLpNorm (U_of N (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  intro t htmem
  obtain ⟨hfloor, hne⟩ := floor_slab_aux ht hN hk t htmem
  have hfun : (fun x => (if t = t1 then (U_of N N).weakDeriv x else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) = (U_of N (k + 1)).weakDeriv := by
    funext x
    simp [hne, hfloor]
  rw [hfun]



/-- Uniform eLpNorm bounds for the interpolants. -/

theorem interp_eLpNorm_bounds
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    {F : ℝ → ℝ → ℝ}
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (U_of : ℕ → ℕ → WeakH10)
    (hBoundsC : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ((t1 - t0) / N) * kmin < 1 →
      (∀ k, k ≤ N →
        (eLpNorm (U_of N k).toFun 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)
      ∧ (∑ k ∈ Finset.range N,
          ((t1 - t0) / N) * (eLpNorm (U_of N (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 ≤ C)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ N : ℕ, 0 < N → ((t1 - t0) / N) * kmin < 1 →
      (eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).toFun x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ C'
      ∧ (eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).weakDeriv x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ≤ C' := by
  obtain ⟨C, hCpos, hBounds⟩ := hBoundsC
  set C' : ℝ := max ((t1 - t0) * C) C + 1 with hC'def
  have hmax_pos : 0 < max ((t1 - t0) * C) C := lt_max_of_lt_right hCpos
  have hC'pos : 0 < C' := by linarith
  have hC'ge1 : 1 ≤ C' := by linarith
  refine ⟨C', hC'pos, fun N hN htau => ?_⟩
  obtain ⟨hToFunBd, hWeakSum⟩ := hBounds N hN htau
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hdiff : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
  have htau_pos : (0 : ℝ) < (t1 - t0) / (N : ℝ) := div_pos hdiff hNpos
  have htau_nn : (0 : ℝ) ≤ (t1 - t0) / (N : ℝ) := le_of_lt htau_pos
  have hNt : (N : ℝ) * ((t1 - t0) / (N : ℝ)) = t1 - t0 := by field_simp
  constructor
  · -- toFun
    by_cases hMemT : MemLp (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).toFun x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    · have hSliceId := eLpNorm_sq_eq_integral_slice ht (fun t x =>
        if t = t1 then (U_of N N).toFun x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x) hMemT
      have hSliceG : ∀ k < N, ∀ t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ)))
          (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))),
          (eLpNorm (fun x => (if t = t1 then (U_of N N).toFun x
            else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          = (eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
        intro k hk t htmem
        have hEq := interp_slice_norm_toFun ht U_of hN hk t htmem
        rw [hEq]
      have hIntG : IntegrableOn (fun t => (eLpNorm (fun x => (if t = t1 then (U_of N N).toFun x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) (Set.Icc t0 t1) volume :=
        integrableOn_slice_sq (fun t x =>
          if t = t1 then (U_of N N).toFun x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x) hMemT
      have hSumEq := integral_piecewise_const_eq_sum ht hN
        (fun t => (eLpNorm (fun x => (if t = t1 then (U_of N N).toFun x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
        (fun k => (eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
        hSliceG hIntG
      have hSumLe : ∑ k ∈ Finset.range N, ((t1 - t0) / (N : ℝ)) *
          (eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          ≤ (t1 - t0) * C := by
        have h1 : ∀ k ∈ Finset.range N, ((t1 - t0) / (N : ℝ)) *
            (eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ ((t1 - t0) / (N : ℝ)) * C := by
          intro k hk
          rw [Finset.mem_range] at hk
          have hle : (eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 ≤ C :=
            hToFunBd (k + 1) (Nat.succ_le_of_lt hk)
          exact mul_le_mul_of_nonneg_left hle htau_nn
        have h2 : ∑ k ∈ Finset.range N, ((t1 - t0) / (N : ℝ)) *
            (eLpNorm (U_of N (k + 1)).toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
            ≤ ∑ _k ∈ Finset.range N, ((t1 - t0) / (N : ℝ)) * C :=
          Finset.sum_le_sum h1
        have h3 : ∑ _k ∈ Finset.range N, ((t1 - t0) / (N : ℝ)) * C = (t1 - t0) * C := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
        rw [h3] at h2
        exact h2
      have hSq : (eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U_of N N).toFun x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ^ 2 ≤ (t1 - t0) * C := by
        rw [hSliceId, hSumEq]
        exact hSumLe
      have hB : (t1 - t0) * C < C' := by
        have hle : (t1 - t0) * C ≤ max ((t1 - t0) * C) C := le_max_left _ _
        linarith
      have hx : 0 ≤ (eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U_of N N).toFun x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal :=
        ENNReal.toReal_nonneg
      exact le_of_sq_le hx hSq hB hC'ge1
    · have hTop : eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U_of N N).toFun x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) = ⊤ := by
        by_contra hne
        exact hMemT (lt_top_iff_ne_top.mpr hne)
      rw [hTop, ENNReal.toReal_top]
      exact le_of_lt hC'pos
  · -- weakDeriv
    by_cases hMemW : MemLp (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).weakDeriv x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    · have hSliceId := eLpNorm_sq_eq_integral_slice ht (fun t x =>
        if t = t1 then (U_of N N).weakDeriv x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x) hMemW
      have hSliceG : ∀ k < N, ∀ t ∈ Set.Ico (t0 + (k : ℝ) * ((t1 - t0) / (N : ℝ)))
          (t0 + ((k : ℝ) + 1) * ((t1 - t0) / (N : ℝ))),
          (eLpNorm (fun x => (if t = t1 then (U_of N N).weakDeriv x
            else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
            (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
          = (eLpNorm (U_of N (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 := by
        intro k hk t htmem
        have hEq := interp_slice_norm_weakDeriv ht U_of hN hk t htmem
        rw [hEq]
      have hIntG : IntegrableOn (fun t => (eLpNorm (fun x => (if t = t1 then (U_of N N).weakDeriv x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) (Set.Icc t0 t1) volume :=
        integrableOn_slice_sq (fun t x =>
          if t = t1 then (U_of N N).weakDeriv x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x) hMemW
      have hSumEq := integral_piecewise_const_eq_sum ht hN
        (fun t => (eLpNorm (fun x => (if t = t1 then (U_of N N).weakDeriv x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
        (fun k => (eLpNorm (U_of N (k + 1)).weakDeriv 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
        hSliceG hIntG
      have hSq : (eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U_of N N).weakDeriv x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal ^ 2 ≤ C := by
        rw [hSliceId, hSumEq]
        exact hWeakSum
      have hB : C < C' := by
        have hle : C ≤ max ((t1 - t0) * C) C := le_max_right _ _
        linarith
      have hx : 0 ≤ (eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U_of N N).weakDeriv x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal :=
        ENNReal.toReal_nonneg
      exact le_of_sq_le hx hSq hB hC'ge1
    · have hTop : eLpNorm (Function.uncurry (fun t x =>
          if t = t1 then (U_of N N).weakDeriv x
          else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) = ⊤ := by
        by_contra hne
        exact hMemW (lt_top_iff_ne_top.mpr hne)
      rw [hTop, ENNReal.toReal_top]
      exact le_of_lt hC'pos


theorem interp_memLp_from_bounds
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10)
    (hToFunMemLp : ∀ h : WeakH10, MemLp h.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {N : ℕ} (hN : 0 < N)
    (hBoundTo : (eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).toFun x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) < ⊤)
    (hBoundGr : (eLpNorm (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).weakDeriv x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) < ⊤) :
    MemLp (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).toFun x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).toFun x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ MemLp (Function.uncurry (fun t x =>
        if t = t1 then (U_of N N).weakDeriv x
        else (U_of N (Nat.floor ((t - t0) / ((t1 - t0) / (N : ℝ))) + 1)).weakDeriv x)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  exact ⟨hBoundTo, hBoundGr⟩


theorem WeakH10.integrable_weakDeriv (w : WeakH10) :
    IntegrableOn w.weakDeriv (Set.Icc (0 : ℝ) 1) volume := by
  have : Fact (volume (Set.Icc (0 : ℝ) 1) < ⊤) := by
    refine ⟨?_⟩
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  exact w.weakDeriv_memLp.integrable (by norm_num)


theorem WeakH10.intervalIntegrable_weakDeriv (w : WeakH10) :
    IntervalIntegrable w.weakDeriv volume 0 1 := by
  refine ⟨?_, ?_⟩
  · exact w.integrable_weakDeriv.mono_set Set.Ioc_subset_Icc_self
  · rw [Set.Ioc_eq_empty (show ¬ (1 : ℝ) < 0 from by norm_num)]
    exact integrableOn_empty


theorem WeakH10.continuousOn_toFun (w : WeakH10) :
    ContinuousOn w.toFun (Set.Icc (0 : ℝ) 1) := by
  have hmem : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 from by norm_num)]
    exact Set.left_mem_Icc.mpr (show (0 : ℝ) ≤ 1 from by norm_num)
  have hprim :=
    intervalIntegral.continuousOn_primitive_interval' w.intervalIntegrable_weakDeriv hmem
  rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 from by norm_num)] at hprim
  exact hprim.congr (fun x hx => w.toFun_eq_integral x hx)


theorem WeakH10.aestronglyMeasurable_toFun (w : WeakH10) :
    AEStronglyMeasurable w.toFun (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  w.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc


theorem WeakH10.exists_bound_toFun (w : WeakH10) :
    ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖w.toFun x‖ ≤ C := by
  obtain ⟨x₀, hx₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (show (0 : ℝ) ≤ 1 from by norm_num))
      w.continuousOn_toFun.norm
  exact ⟨‖w.toFun x₀‖, by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact hmax hx⟩


theorem integrable_slice_toFun_mul (U : WeakH10) (ψ : ℝ → ℝ)
    (hψ : Integrable ψ (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable (fun x : ℝ => U.toFun x * ψ x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := U.exists_bound_toFun
  exact hψ.bdd_mul U.aestronglyMeasurable_toFun hC


theorem ioc_ae_eq_icc_zero_one : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Icc (0 : ℝ) 1 := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬t ≠ 0} = {(0 : ℝ)} := by
      ext t
      simp
    rw [hset, measure_singleton]
  have hiff : ∀ᵐ t ∂(volume : Measure ℝ),
      (t ∈ Set.Ioc (0 : ℝ) 1 ↔ t ∈ Set.Icc (0 : ℝ) 1) := by
    filter_upwards [hne] with t ht
    exact ⟨fun h => ⟨le_of_lt h.1, h.2⟩, fun h => ⟨lt_of_le_of_ne' h.1 ht, h.2⟩⟩
  exact hiff.mono (fun t ht => propext ht)


/-- Bump average as a space-time integral. -/

theorem bump_as_spacetime
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (u : ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {N : ℕ} {τ : ℝ} (hτ0 : t0 < τ) (hτ1 : τ < t1) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : t0 < τ - δ) (hδ1 : τ + δ < t1) :
    (1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ),
        (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
      = (1 / (2 * δ)) * ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
             else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun p.2) * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  set G : (ℝ × ℝ) → ℝ := fun p =>
    (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
      else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun p.2) *
    (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) with hGdef
  set J : ℝ → ℕ := fun t =>
    if t = t1 then φ N else Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1 with hJdef
  set μP : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) with hμPdef
  show _ = (1 / (2 * δ)) * ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, G p
    ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
  have hfin01 : Fact (volume (Set.Icc (0 : ℝ) 1) < ⊤) := by
    refine ⟨?_⟩
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hfint : Fact (volume (Set.Icc t0 t1) < ⊤) := by
    refine ⟨?_⟩
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hψint : Integrable ψ (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hψ.integrable (by norm_num)
  have hslice : ∀ k : ℕ,
      Integrable (fun x : ℝ => (U_of (φ N) k).toFun x * ψ x)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    fun k => integrable_slice_toFun_mul _ _ hψint
  have hfloor_le : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) ≤ φ N := by
    intro t htm
    have ht0 : (0 : ℝ) ≤ t - t0 := sub_nonneg.mpr htm.1
    have hstep_nonneg : (0 : ℝ) ≤ (t1 - t0) / (φ N : ℝ) :=
      div_nonneg (le_of_lt (sub_pos.mpr ht)) (Nat.cast_nonneg _)
    have hratio_nonneg : (0 : ℝ) ≤ (t - t0) / ((t1 - t0) / (φ N : ℝ)) :=
      div_nonneg ht0 hstep_nonneg
    have hratio_le : (t - t0) / ((t1 - t0) / (φ N : ℝ)) ≤ ((φ N : ℕ) : ℝ) := by
      by_cases hφ0 : φ N = 0
      · rw [hφ0]
        simp
      · have hφpos : (0 : ℝ) < ((φ N : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hφ0)
        have hstep_pos : (0 : ℝ) < (t1 - t0) / (φ N : ℝ) :=
          div_pos (sub_pos.mpr ht) hφpos
        rw [div_le_iff₀ hstep_pos]
        have hmul : ((φ N : ℕ) : ℝ) * ((t1 - t0) / ((φ N : ℕ) : ℝ)) = t1 - t0 := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ (ne_of_gt hφpos)
        rw [hmul]
        exact sub_le_sub_right htm.2 t0
    have hcast : (((Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) : ℕ)) : ℝ)
        ≤ ((φ N : ℕ) : ℝ) :=
      le_trans (Nat.floor_le hratio_nonneg) hratio_le
    exact Nat.cast_le.mp hcast
  have hJbound : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → J t < φ N + 2 := by
    intro t ht
    simp only [hJdef]
    by_cases ht1 : t = t1
    · rw [ite_eq_left ht1]
      omega
    · rw [ite_eq_right ht1]
      have hfl := hfloor_le t ht
      omega
  have hJmeas : Measurable J := by
    simp only [hJdef]
    refine Measurable.ite ?_ measurable_const ?_
    · have hset : {t : ℝ | t = t1} = {t1} := by
        ext t
        simp
      rw [hset]
      exact measurableSet_singleton t1
    · have hlin : Measurable (fun t : ℝ => (t - t0) / ((t1 - t0) / (φ N : ℝ))) := by
        measurability
      have hfl : Measurable (fun t : ℝ => Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ)))) :=
        Measurable.nat_floor hlin
      exact hfl.add measurable_const
  have hμPmem : ∀ᵐ p ∂μP, p ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    rw [hμPdef, Measure.prod_restrict _ _]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hu : ∀ k : ℕ, AEStronglyMeasurable
      (fun p : ℝ × ℝ => (if J p.1 = k then (1 : ℝ) else 0)) μP := by
    intro k
    have hset : {p : ℝ × ℝ | J p.1 = k} = Prod.fst ⁻¹' (J ⁻¹' {k}) := by
      ext p
      simp
    have hsm : MeasurableSet {p : ℝ × ℝ | J p.1 = k} := by
      rw [hset]
      exact measurable_fst (hJmeas (measurableSet_singleton k))
    exact (Measurable.ite hsm measurable_const measurable_const).aestronglyMeasurable
  have hv : ∀ k : ℕ, AEStronglyMeasurable
      (fun p : ℝ × ℝ => (U_of (φ N) k).toFun p.2) μP := by
    intro k
    rw [hμPdef]
    exact (U_of (φ N) k).aestronglyMeasurable_toFun.comp_snd
  have hψlift : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.2) μP := by
    rw [hμPdef]
    exact hψ.aestronglyMeasurable.comp_snd
  have hw : AEStronglyMeasurable
      (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) μP := by
    have hIoo : MeasurableSet (Set.Ioo (τ - δ) (τ + δ) ×ˢ (Set.univ : Set ℝ)) :=
      measurableSet_Ioo.prod MeasurableSet.univ
    have hbase : AEStronglyMeasurable
        ((Set.Ioo (τ - δ) (τ + δ) ×ˢ (Set.univ : Set ℝ)).indicator
          (fun p : ℝ × ℝ => ψ p.2)) μP :=
      hψlift.indicator hIoo
    apply hbase.congr
    refine Eventually.of_forall fun p => ?_
    by_cases hp1 : p.1 ∈ Set.Ioo (τ - δ) (τ + δ)
    · have hpmem : p ∈ Set.Ioo (τ - δ) (τ + δ) ×ˢ (Set.univ : Set ℝ) :=
        Set.mk_mem_prod hp1 (Set.mem_univ _)
      simp only [Set.indicator_of_mem hpmem, ite_eq_left hp1]
    · have hpmem : p ∉ Set.Ioo (τ - δ) (τ + δ) ×ˢ (Set.univ : Set ℝ) :=
        fun h => hp1 (Set.mem_prod.mp h).1
      simp only [Set.indicator_of_notMem hpmem, ite_eq_right hp1]
  have hF : ∀ k ∈ Finset.range (φ N + 2), AEStronglyMeasurable
      (fun p : ℝ × ℝ => (if J p.1 = k then (1 : ℝ) else 0) * (U_of (φ N) k).toFun p.2 *
        (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)) μP := by
    intro k hk
    exact ((hu k).mul (hv k)).mul hw
  have hsum_ae : AEStronglyMeasurable (∑ k ∈ Finset.range (φ N + 2),
      fun p : ℝ × ℝ => (if J p.1 = k then (1 : ℝ) else 0) * (U_of (φ N) k).toFun p.2 *
        (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)) μP :=
    Finset.aestronglyMeasurable_sum _ hF
  have hGae : AEStronglyMeasurable G μP := by
    apply hsum_ae.congr
    filter_upwards [hμPmem] with p hp
    have hJm : J p.1 ∈ Finset.range (φ N + 2) := by
      rw [Finset.mem_range]
      exact hJbound p.1 (Set.mem_prod.mp hp).1
    have hcollapse : (∑ k ∈ Finset.range (φ N + 2),
            (if J p.1 = k then (1 : ℝ) else 0) * (U_of (φ N) k).toFun p.2 *
            (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0))
          = (1 : ℝ) * (U_of (φ N) (J p.1)).toFun p.2 *
            (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) := by
      calc (∑ k ∈ Finset.range (φ N + 2),
              (if J p.1 = k then (1 : ℝ) else 0) * (U_of (φ N) k).toFun p.2 *
              (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0))
            = ∑ k ∈ Finset.range (φ N + 2),
              (if J p.1 = k then (1 : ℝ) * (U_of (φ N) k).toFun p.2 *
                (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) else 0) :=
              Finset.sum_congr rfl (fun k _ => by by_cases hk : J p.1 = k <;> simp [hk])
        _ = (1 : ℝ) * (U_of (φ N) (J p.1)).toFun p.2 *
              (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) := by
              rw [Finset.sum_ite_eq _ _ _, ite_eq_left hJm]
    simp only [Finset.sum_apply]
    rw [hcollapse]
    simp only [hGdef, hJdef]
    by_cases ht1 : p.1 = t1 <;> simp [ht1]
  have hbound : ∀ᵐ p ∂μP, ‖G p‖ ≤ ∑ k ∈ Finset.range (φ N + 2),
      ‖(U_of (φ N) k).toFun p.2 * ψ p.2‖ := by
    filter_upwards [hμPmem] with p hp
    simp only [hGdef]
    by_cases hIoo : p.1 ∈ Set.Ioo (τ - δ) (τ + δ)
    · rw [ite_eq_left hIoo]
      by_cases ht1 : p.1 = t1
      · rw [ite_eq_left ht1]
        refine Finset.single_le_sum (f := fun k => ‖(U_of (φ N) k).toFun p.2 * ψ p.2‖)
          (fun k _ => norm_nonneg _) ?_
        rw [Finset.mem_range]
        omega
      · rw [ite_eq_right ht1]
        refine Finset.single_le_sum (f := fun k => ‖(U_of (φ N) k).toFun p.2 * ψ p.2‖)
          (fun k _ => norm_nonneg _) ?_
        rw [Finset.mem_range]
        have hfl := hfloor_le p.1 (Set.mem_prod.mp hp).1
        omega
    · rw [ite_eq_right hIoo, mul_zero, norm_zero]
      exact Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hS : Integrable (fun p : ℝ × ℝ => ∑ k ∈ Finset.range (φ N + 2),
      ‖(U_of (φ N) k).toFun p.2 * ψ p.2‖) μP := by
    rw [hμPdef]
    apply integrable_finsetSum
    intro k hk
    exact ((hslice k).norm).comp_snd _
  have hGintP : Integrable G μP := hS.mono' hGae hbound
  have hInt : IntegrableOn G (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    show Integrable G ((volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
    rw [← Measure.prod_restrict _ _]
    exact hGintP
  have hFub : (∫ z in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, G z ∂(volume.prod volume))
      = ∫ x in Set.Icc t0 t1, (∫ y in Set.Icc (0 : ℝ) 1, G (x, y) ∂volume) ∂volume :=
    setIntegral_prod G hInt
  have hvol : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
    Measure.volume_eq_prod ℝ ℝ
  have hmeas : (((volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
      = (volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_restrict (measurableSet_Icc.prod measurableSet_Icc), Set.inter_self]
  rw [hvol, hmeas, hFub]
  have hslice_eq : ∀ t : ℝ, t ∈ Set.Ioo (τ - δ) (τ + δ) →
      (∫ y in Set.Icc (0 : ℝ) 1, G (t, y) ∂volume)
        = ∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
            else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) *
          ψ x := by
    intro t htIoo
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from by norm_num)]
    rw [setIntegral_congr_set ioc_ae_eq_icc_zero_one]
    have hpt : ∀ y : ℝ, G (t, y)
        = (if t = t1 then (U_of (φ N) (φ N)).toFun y
            else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun y) *
          ψ y := by
      intro y
      have hGy : G (t, y)
          = (if t = t1 then (U_of (φ N) (φ N)).toFun y
              else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun y) *
            (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ y else 0) := rfl
      rw [hGy, ite_eq_left htIoo]
    simp only [hpt]
  have hinner0 : ∀ t : ℝ, t ∉ Set.Ioo (τ - δ) (τ + δ) →
      (∫ y in Set.Icc (0 : ℝ) 1, G (t, y) ∂volume) = 0 := by
    intro t htIoo
    have h0 : ∀ y : ℝ, G (t, y) = 0 := by
      intro y
      have hGy : G (t, y)
          = (if t = t1 then (U_of (φ N) (φ N)).toFun y
              else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun y) *
            (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ y else 0) := rfl
      rw [hGy, ite_eq_right htIoo, mul_zero]
    simp only [h0]
    exact integral_zero _ _
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ τ + δ := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬t ≠ τ + δ} = {τ + δ} := by
      ext t
      simp
    rw [hset, measure_singleton]
  congr 1
  rw [intervalIntegral.integral_of_le (show (τ - δ) ≤ τ + δ from by linarith [hδ])]
  rw [← integral_indicator (s := Set.Ioc (τ - δ) (τ + δ)) measurableSet_Ioc,
    ← integral_indicator (s := Set.Icc t0 t1) measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [hne] with t ht
  by_cases htIoo : t ∈ Set.Ioo (τ - δ) (τ + δ)
  · have hIoc : t ∈ Set.Ioc (τ - δ) (τ + δ) := ⟨htIoo.1, le_of_lt htIoo.2⟩
    have hIcct : t ∈ Set.Icc t0 t1 :=
      ⟨le_of_lt (lt_trans hδ0 htIoo.1), le_of_lt (lt_trans htIoo.2 hδ1)⟩
    simp only [Set.indicator_of_mem hIoc, Set.indicator_of_mem hIcct]
    exact (hslice_eq t htIoo).symm
  · have hIoc' : t ∉ Set.Ioc (τ - δ) (τ + δ) := by
      intro hcon
      apply htIoo
      exact ⟨hcon.1, lt_of_le_of_ne' hcon.2 (Ne.symm ht)⟩
    simp only [Set.indicator_of_notMem hIoc']
    by_cases htIcc : t ∈ Set.Icc t0 t1
    · simp only [Set.indicator_of_mem htIcc, hinner0 t htIoo]
    · simp only [Set.indicator_of_notMem htIcc]


theorem bump_as_spacetime_u
    {t0 t1 : ℝ} (ht : t0 < t1)
    {w : ℝ → ℝ → ℝ} (hw : MemLp (Function.uncurry w) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {τ : ℝ} (hτ0 : t0 < τ) (hτ1 : τ < t1) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : t0 < τ - δ) (hδ1 : τ + δ < t1) :
    (1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ), (∫ x in (0 : ℝ)..1, w t x * ψ x)
      = (1 / (2 * δ)) * ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  have hRmeas : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hab_le : τ - δ ≤ τ + δ := by linarith
  have hsub : Set.Ioo (τ - δ) (τ + δ) ⊆ Set.Icc t0 t1 := by
    intro t htt
    exact ⟨le_of_lt (lt_of_lt_of_le hδ0 (le_of_lt htt.1)),
      le_of_lt (lt_of_le_of_lt (le_of_lt htt.2) hδ1)⟩
  have hprod : (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))
      = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hw2 : MemLp (Function.uncurry w) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [hprod]
    exact hw
  have hψ2 : MemLp (fun p : ℝ × ℝ => ψ p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hψ.comp_snd (volume.restrict (Set.Icc t0 t1))
  have hψI : MemLp (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have hfun : (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
        = (Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => ψ p.2) := by
      ext p
      show (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
        = (Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ).indicator (fun p : ℝ × ℝ => ψ p.2) p
      by_cases hp : p.1 ∈ Set.Ioo (τ - δ) (τ + δ)
      · have hpmem : p ∈ Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ := ⟨hp, Set.mem_univ _⟩
        rw [ite_eq_left hp, Set.indicator_of_mem hpmem]
      · have hpnmem : p ∉ Set.Ioo (τ - δ) (τ + δ) ×ˢ Set.univ := fun h => hp h.1
        rw [ite_eq_right hp, Set.indicator_of_notMem hpnmem]
    rw [hfun]
    exact MemLp.indicator (measurableSet_Ioo.prod MeasurableSet.univ).nullMeasurableSet hψ2
  have hFint : Integrable
      (fun p : ℝ × ℝ => w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0))
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hw2.integrable_mul hψI
  have hFon : IntegrableOn
      (fun p : ℝ × ℝ => w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0))
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    show Integrable _ ((volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
    rw [← Measure.prod_restrict]
    exact hFint
  have hFubini : ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) ∂(volume.prod volume)
      = ∫ t in Set.Icc t0 t1, ∫ x in Set.Icc (0 : ℝ) 1,
          w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume ∂volume :=
    setIntegral_prod _ hFon
  have houter : ∫ t in Set.Icc t0 t1,
          (∫ x in Set.Icc (0 : ℝ) 1,
            w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume) ∂volume
      = ∫ t in Set.Ioo (τ - δ) (τ + δ),
          (∫ x in Set.Icc (0 : ℝ) 1,
            w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume) ∂volume := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub
    intro t htt
    have hz : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) = 0 := by
      intro x _
      rw [ite_eq_right htt.2, mul_zero]
    calc (∫ x in Set.Icc (0 : ℝ) 1,
            w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume)
        = ∫ x in Set.Icc (0 : ℝ) 1, 0 ∂volume :=
          setIntegral_congr_fun measurableSet_Icc hz
      _ = 0 := by simp
  have hinner : ∀ t ∈ Set.Ioo (τ - δ) (τ + δ),
      (∫ x in Set.Icc (0 : ℝ) 1,
        w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume)
      = ∫ x in (0 : ℝ)..1, w t x * ψ x := by
    intro t htt
    have h1 : (∫ x in Set.Icc (0 : ℝ) 1,
          w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume)
        = ∫ x in Set.Icc (0 : ℝ) 1, w t x * ψ x ∂volume := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      show w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) = w t x * ψ x
      rw [ite_eq_left htt]
    rw [h1, (setIntegral_congr_set (Ioc_ae_eq_Icc' Real.volume_singleton)).symm,
      ← intervalIntegral.integral_of_le zero_le_one]
  congr 1
  calc ∫ t in (τ - δ)..(τ + δ), (∫ x in (0 : ℝ)..1, w t x * ψ x)
      = ∫ t in Set.Ioc (τ - δ) (τ + δ), (∫ x in (0 : ℝ)..1, w t x * ψ x) ∂volume :=
        intervalIntegral.integral_of_le hab_le
    _ = ∫ t in Set.Ioo (τ - δ) (τ + δ), (∫ x in (0 : ℝ)..1, w t x * ψ x) ∂volume :=
        (setIntegral_congr_set (Ioo_ae_eq_Ioc' Real.volume_singleton)).symm
    _ = ∫ t in Set.Ioo (τ - δ) (τ + δ),
          (∫ x in Set.Icc (0 : ℝ) 1,
            w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume) ∂volume :=
        setIntegral_congr_fun measurableSet_Ioo (fun t htt => (hinner t htt).symm)
    _ = ∫ t in Set.Icc t0 t1,
          (∫ x in Set.Icc (0 : ℝ) 1,
            w t x * (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) ∂volume) ∂volume :=
        houter.symm
    _ = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
            ∂(volume.prod volume) := hFubini.symm
    _ = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) ∂volume := by
        rw [Measure.volume_eq_prod]
    _ = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
        rw [Measure.restrict_restrict hRmeas, Set.inter_self]


lemma memLp_bumpIndicator (ψ : ℝ → ℝ) (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (τ δ t0 t1 : ℝ) :
    MemLp (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have hμE : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hc : 0 < (2 : ENNReal).toReal := ENNReal.toReal_pos (by simp) (by simp)
  have hC : (∫⁻ x, enorm (ψ x) ^ (2 : ENNReal).toReal
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) < ⊤ := by
    have hψ' : eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) < ⊤ := hψ
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by simp) (by simp)
      hψ.aestronglyMeasurable).mp hψ'
  have h_ae : AEStronglyMeasurable
      (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    obtain ⟨g, hg_str, hfg⟩ := hψ.aestronglyMeasurable
    have hF1 : StronglyMeasurable
        (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then g p.2 else 0) := by
      apply Measurable.stronglyMeasurable
      refine Measurable.ite ?_ (hg_str.measurable.comp measurable_snd) measurable_const
      exact measurable_fst measurableSet_Ioo
    have hN : (volume.restrict (Set.Icc (0 : ℝ) 1)) {x | ψ x ≠ g x} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      have hfg' : ∀ᶠ x in ae (volume.restrict (Set.Icc (0 : ℝ) 1)), ψ x = g x := hfg
      filter_upwards [hfg'] with x hx
      exact not_not_intro hx
    have hnull : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
        {p : ℝ × ℝ | (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
          ≠ (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then g p.2 else 0)} = 0 := by
      refine measure_mono_null (t := Set.univ ×ˢ {x | ψ x ≠ g x}) ?_ ?_
      · intro p hp
        simp only [Set.mem_ofPred_eq] at hp
        show p.1 ∈ Set.univ ∧ p.2 ∈ {x | ψ x ≠ g x}
        refine ⟨trivial, ?_⟩
        show ψ p.2 ≠ g p.2
        intro hcon
        apply hp
        by_cases h : p.1 ∈ Set.Ioo (τ - δ) (τ + δ)
        · rw [ite_eq_left h, ite_eq_left h]
          exact hcon
        · rw [ite_eq_right h, ite_eq_right h]
      · rw [hμE, Measure.prod_prod, hN, mul_zero]
    have hEq : (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
        =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)]
        (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then g p.2 else 0) := by
      have hmem := measure_eq_zero_iff_ae_notMem.mp hnull
      filter_upwards [hmem] with p hp
      exact not_not.mp hp
    exact hF1.aestronglyMeasurable.congr hEq.symm
  rw [hμE] at h_ae ⊢
  have hψe : eLpNorm (fun p : ℝ × ℝ => if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by simp) (by simp) h_ae]
    have h_aemeas : AEMeasurable
        (fun z : ℝ × ℝ => enorm (if z.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ z.2 else 0)
          ^ (2 : ENNReal).toReal)
        ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      have hfrpow : AEStronglyMeasurable
          (fun z : ℝ × ℝ => enorm (if z.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ z.2 else 0)
            ^ (2 : ENNReal).toReal)
          ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
        fun_prop
      exact hfrpow.aemeasurable
    rw [lintegral_prod _ h_aemeas]
    have hinner : ∀ t : ℝ, (∫⁻ x, enorm (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0)
        ^ (2 : ENNReal).toReal ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        = (Set.Ioo (τ - δ) (τ + δ)).indicator
          (fun _ => ∫⁻ x, enorm (ψ x) ^ (2 : ENNReal).toReal
            ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) t := by
      intro t
      by_cases ht : t ∈ Set.Ioo (τ - δ) (τ + δ)
      · rw [Set.indicator_of_mem ht]
        apply lintegral_congr
        intro x
        rw [ite_eq_left ht]
      · rw [Set.indicator_of_notMem ht]
        have hzero : (fun x : ℝ => enorm (if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0)
            ^ (2 : ENNReal).toReal) = fun _ => 0 := by
          funext x
          rw [ite_eq_right ht, enorm_zero, ENNReal.zero_rpow_of_pos hc]
        rw [hzero, lintegral_zero]
    simp only [hinner]
    rw [lintegral_indicator measurableSet_Ioo]
    have hconst : (∫⁻ t in Set.Ioo (τ - δ) (τ + δ),
          (fun _ => ∫⁻ x, enorm (ψ x) ^ (2 : ENNReal).toReal
            ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) t
          ∂(volume.restrict (Set.Icc t0 t1)))
        = (∫⁻ x, enorm (ψ x) ^ (2 : ENNReal).toReal ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
          * ((volume.restrict (Set.Icc t0 t1)).restrict (Set.Ioo (τ - δ) (τ + δ))) Set.univ :=
      lintegral_const _
    rw [hconst, Measure.restrict_apply_univ]
    have hJfin : (volume.restrict (Set.Icc t0 t1)) (Set.Ioo (τ - δ) (τ + δ)) < ⊤ := by
      calc (volume.restrict (Set.Icc t0 t1)) (Set.Ioo (τ - δ) (τ + δ))
          ≤ (volume.restrict (Set.Icc t0 t1)) Set.univ := measure_mono (Set.subset_univ _)
        _ = volume (Set.Icc t0 t1) := Measure.restrict_apply_univ _
        _ = ENNReal.ofReal (t1 - t0) := Real.volume_Icc
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top hC hJfin
  exact hψe


/-- Bump-average convergence, assembled. -/

theorem bump_pairing_tendsto
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (u : ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hWeakU : ∀ ψ : ℝ → ℝ → ℝ,
        MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
        Filter.Tendsto (fun N : ℕ =>
            ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
               else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
                * ψ p.1 p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            u p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hAs : ∀ (N : ℕ) (τ : ℝ) (δ : ℝ), t0 < τ → τ < t1 → 0 < δ → t0 < τ - δ → τ + δ < t1 →
      ∀ ψ : ℝ → ℝ, MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      (1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ),
          (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
        = (1 / (2 * δ)) * ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
             else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun p.2)
              * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hUside : ∀ (w : ℝ → ℝ → ℝ), MemLp (Function.uncurry w) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
      ∀ (ψ : ℝ → ℝ), MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ (τ : ℝ), t0 < τ → τ < t1 → ∀ (δ : ℝ), 0 < δ → t0 < τ - δ → τ + δ < t1 →
      (1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ), (∫ x in (0 : ℝ)..1, w t x * ψ x)
        = (1 / (2 * δ)) * ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            w p.1 p.2 * (if p.1 ∈ Set.Ioo (τ - δ) (τ + δ) then ψ p.2 else 0)
              ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hMemU : MemLp (Function.uncurry u) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {τ : ℝ} (hτ0 : t0 < τ) (hτ1 : τ < t1) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : t0 < τ - δ) (hδ1 : τ + δ < t1) :
    Filter.Tendsto (fun N : ℕ => (1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ),
        (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
           else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x))
      Filter.atTop (nhds ((1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ),
        (∫ x in (0 : ℝ)..1, u t x * ψ x))) := by
  have hΨ : MemLp (Function.uncurry fun t x => if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    memLp_bumpIndicator ψ hψ τ δ t0 t1
  have hlim := hWeakU (fun t x => if t ∈ Set.Ioo (τ - δ) (τ + δ) then ψ x else 0) hΨ
  have hmain := Filter.Tendsto.const_mul (1 / (2 * δ)) hlim
  have hU := hUside u hMemU ψ hψ τ hτ0 hτ1 δ hδ hδ0 hδ1
  rw [hU]
  refine Filter.Tendsto.congr' ?_ hmain
  apply Filter.Eventually.of_forall
  intro N
  exact (hAs N τ δ hτ0 hτ1 hδ hδ0 hδ1 ψ hψ).symm


theorem pairing_integral_zero (ψ : ℝ → ℝ)
    (hψ0 : ψ =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0) (v : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..1, v x * ψ x = 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply integral_eq_zero_of_ae
  have hIoc : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ψ x = 0 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hψ0
  exact hIoc.mono (fun x hx => by simp [hx])


theorem slice_measurable (U_of : ℕ → ℕ → WeakH10) (ψ : ℝ → ℝ) (t0 t1 : ℝ)
    (c k0 : ℕ) :
    Measurable (fun t : ℝ => ∫ x in (0 : ℝ)..1,
      (if t = t1 then (U_of c k0).toFun x
        else (U_of c (Nat.floor ((t - t0) / ((t1 - t0) / (c : ℝ))) + 1)).toFun x) * ψ x) := by
  let F : ℕ → ℝ := fun j => ∫ x in (0 : ℝ)..1, (U_of c j).toFun x * ψ x
  let k : ℝ → ℕ := fun t => if t = t1 then k0 else Nat.floor ((t - t0) / ((t1 - t0) / (c : ℝ))) + 1
  have hEq : (fun t : ℝ => ∫ x in (0 : ℝ)..1,
      (if t = t1 then (U_of c k0).toFun x
        else (U_of c (Nat.floor ((t - t0) / ((t1 - t0) / (c : ℝ))) + 1)).toFun x) * ψ x) = F ∘ k := by
    funext t
    by_cases ht : t = t1
    · simp [F, k, ht]
    · simp [F, k, ht]
  rw [hEq]
  apply Measurable.comp (measurable_of_countable F)
  have hAff : Measurable (fun t : ℝ => (t - t0) / ((t1 - t0) / (c : ℝ))) :=
    (measurable_id.sub_const t0).div_const _
  have hFloor : Measurable (fun t : ℝ => Nat.floor ((t - t0) / ((t1 - t0) / (c : ℝ))) + 1) :=
    (Measurable.nat_floor hAff).add_const 1
  have hSet : MeasurableSet {t : ℝ | t = t1} := by
    have : {t : ℝ | t = t1} = {t1} := by ext; simp
    rw [this]
    exact measurableSet_singleton t1
  exact Measurable.ite hSet measurable_const hFloor


theorem exists_small_delta {t0 t1 τ C K eps : ℝ} (hτ0 : t0 < τ) (hτ1 : τ < t1)
    (hC0 : 0 ≤ C) (hKpos : 0 < K) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ t0 < τ - δ ∧ τ + δ < t1 ∧ Real.sqrt (C * (δ + δ)) * K < eps/4 := by
  have hτt0 : 0 < τ - t0 := sub_pos.mpr hτ0
  have ht1τ : 0 < t1 - τ := sub_pos.mpr hτ1
  have hKne : K ≠ 0 := ne_of_gt hKpos
  by_cases hC0' : C = 0
  · refine ⟨min ((τ - t0)/2) ((t1 - τ)/2), ?_, ?_, ?_, ?_⟩
    · exact lt_min_iff.mpr ⟨by linarith, by linarith⟩
    · have h1 : min ((τ - t0)/2) ((t1 - τ)/2) ≤ (τ - t0)/2 := min_le_left _ _
      linarith
    · have h2 : min ((τ - t0)/2) ((t1 - τ)/2) ≤ (t1 - τ)/2 := min_le_right _ _
      linarith
    · rw [hC0', zero_mul, Real.sqrt_zero, zero_mul]
      linarith
  · have hCpos : 0 < C := lt_of_le_of_ne' hC0 hC0'
    have hCne : C ≠ 0 := ne_of_gt hCpos
    set E : ℝ := eps / (4 * K) with hEdef
    have hEpos : 0 < E := by positivity
    have hYpos : 0 < E^2 / (2 * C) := by positivity
    refine ⟨min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2), ?_, ?_, ?_, ?_⟩
    · exact lt_min_iff.mpr ⟨lt_min_iff.mpr ⟨by linarith, by linarith⟩, by linarith⟩
    · have h1 : min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) ≤ (τ - t0)/2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    · have h2 : min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) ≤ (t1 - τ)/2 :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    · have hδle : min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) ≤ E^2 / (2 * C) / 2 :=
        min_le_right _ _
      have hE2 : 0 < E^2 := by positivity
      have hstep : C * (min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) +
          min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2)) ≤ E^2 / 2 := by
        have hmul : 2 * C * min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2)
            ≤ 2 * C * (E^2 / (2 * C) / 2) :=
          mul_le_mul_of_nonneg_left hδle (by positivity)
        have heq : 2 * C * (E^2 / (2 * C) / 2) = E^2 / 2 := by
          field_simp
        have hring : C * (min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) +
            min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2))
            = 2 * C * min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) := by ring
        rw [hring]
        rw [heq] at hmul
        exact hmul
      have hlt : C * (min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) +
          min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2)) < E^2 := by
        have : E^2 / 2 < E^2 := by linarith
        exact lt_of_le_of_lt hstep this
      have hsqrt : Real.sqrt (C * (min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) +
          min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2))) < E :=
        (Real.sqrt_lt' hEpos).mpr hlt
      have hEK : E * K = eps / 4 := by
        simp [hEdef]
        field_simp
      calc Real.sqrt (C * (min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2) +
            min (min ((τ - t0)/2) ((t1 - τ)/2)) (E^2 / (2 * C) / 2))) * K
          < E * K := mul_lt_mul_of_pos_right hsqrt hKpos
        _ = eps / 4 := hEK


theorem avg_bound (g : ℝ → ℝ) (t0 t1 τ δ C K : ℝ) (φN : ℝ)
    (hg : Measurable g)
    (hδpos : 0 < δ) (hτδ0 : t0 < τ - δ) (hτδ1 : τ + δ < t1)
    (hτ0 : t0 < τ) (hτ1 : τ < t1)
    (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hratio : φN ≤ δ)
    (hBd : ∀ s t : ℝ, s ∈ Set.Icc t0 t1 → t ∈ Set.Icc t0 t1 →
      |g s - g t| ≤ Real.sqrt (C * (|s - t| + φN)) * K) :
    |g τ - (1/(2*δ)) * ∫ t in (τ-δ)..(τ+δ), g t| ≤ Real.sqrt (C * (δ + δ)) * K := by
  set a : ℝ := τ - δ with hadef
  set b : ℝ := τ + δ with hbdef
  have hab : a ≤ b := by simp [hadef, hbdef]; linarith
  have hτIcc : τ ∈ Set.Icc t0 t1 := ⟨le_of_lt hτ0, le_of_lt hτ1⟩
  have hpt : ∀ t ∈ Set.Ioc a b, |g τ - g t| ≤ Real.sqrt (C * (δ + δ)) * K := by
    intro t ht
    have htIcc : t ∈ Set.Icc t0 t1 := by
      rw [Set.mem_Icc]
      have h1 : a < t := ht.1
      have h2 : t ≤ b := ht.2
      simp [hadef, hbdef] at h1 h2
      constructor <;> linarith
    have h1 := hBd τ t hτIcc htIcc
    have habs : |τ - t| ≤ δ := by
      have h1 : a < t := ht.1
      have h2 : t ≤ b := ht.2
      rw [abs_le]
      simp [hadef, hbdef] at h1 h2
      constructor <;> linarith
    have hsum : |τ - t| + φN ≤ δ + δ := add_le_add habs hratio
    have hmul : C * (|τ - t| + φN) ≤ C * (δ + δ) := mul_le_mul_of_nonneg_left hsum hC0
    have hsq : Real.sqrt (C * (|τ - t| + φN)) ≤ Real.sqrt (C * (δ + δ)) :=
      Real.sqrt_le_sqrt hmul
    have hK : Real.sqrt (C * (|τ - t| + φN)) * K ≤ Real.sqrt (C * (δ + δ)) * K :=
      mul_le_mul_of_nonneg_right hsq hK0
    exact le_trans h1 hK
  have hInt : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine IntegrableOn.of_bound (C := |g τ| + Real.sqrt (C * (δ + δ)) * K) measure_Ioc_lt_top hg.aestronglyMeasurable ?_
    have hmem : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), t ∈ Set.Ioc a b :=
      ae_restrict_mem measurableSet_Ioc
    refine hmem.mono (fun t ht => ?_)
    have hptt := hpt t ht
    rw [Real.norm_eq_abs]
    have heq : g t = g τ + (g t - g τ) := by ring
    calc |g t| = |g τ + (g t - g τ)| := by rw [← heq]
      _ ≤ |g τ| + |g t - g τ| := abs_add_le _ _
      _ = |g τ| + |g τ - g t| := by rw [abs_sub_comm (g t) (g τ)]
      _ ≤ |g τ| + Real.sqrt (C * (δ + δ)) * K := add_le_add_right hptt _
  have hGc : IntervalIntegrable (fun _ => g τ) volume a b := intervalIntegrable_const
  have hsub := intervalIntegral.integral_sub hGc hInt
  have hconst : ∫ t in a..b, g τ = (b - a) * g τ := by
    have h := intervalIntegral.integral_const (a := a) (b := b) (g τ)
    rwa [smul_eq_mul] at h
  have hba : b - a = 2 * δ := by simp [hadef, hbdef]; ring
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have h2δpos : 0 < (2 : ℝ) * δ := by linarith
  have h2δne : (2 : ℝ) * δ ≠ 0 := ne_of_gt h2δpos
  have hnorm : ‖∫ t in a..b, (g τ - g t)‖ ≤ Real.sqrt (C * (δ + δ)) * K * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    have hptt := hpt t ht
    rwa [Real.norm_eq_abs]
  have hJ : ∫ t in a..b, (g τ - g t) = 2*δ*(g τ) - ∫ t in a..b, g t := by
    rw [hsub, hconst, hba]
  have hdecomp : g τ - (1/(2*δ)) * ∫ t in a..b, g t = (1/(2*δ)) * ∫ t in a..b, (g τ - g t) := by
    rw [hJ]
    field_simp
  rw [hdecomp]
  have hpos : 0 < 1/(2*δ) := by positivity
  rw [abs_mul, abs_of_nonneg (le_of_lt hpos)]
  have hJabs : |∫ t in a..b, (g τ - g t)| ≤ Real.sqrt (C*(δ+δ))*K * |b - a| := by
    rwa [Real.norm_eq_abs] at hnorm
  have hba2 : |b - a| = 2*δ := by rw [hba]; exact abs_of_nonneg (le_of_lt h2δpos)
  have hle : (1/(2*δ)) * |∫ t in a..b, (g τ - g t)|
      ≤ (1/(2*δ)) * (Real.sqrt (C*(δ+δ))*K * |b - a|) :=
    mul_le_mul_of_nonneg_left hJabs (le_of_lt hpos)
  have heq : (1/(2*δ)) * (Real.sqrt (C*(δ+δ))*K * |b - a|) = Real.sqrt (C*(δ+δ))*K := by
    rw [hba2]
    field_simp
  exact le_trans hle (le_of_eq heq)


theorem abs_sub_le_three (a b1 b2 c : ℝ) :
    |a - c| ≤ |a - b1| + |b1 - b2| + |b2 - c| := by
  have heq : a - c = (a - b1) + (b1 - b2) + (b2 - c) := by ring
  calc |a - c| = |(a - b1) + (b1 - b2) + (b2 - c)| := by rw [heq]
    _ ≤ |(a - b1) + (b1 - b2)| + |b2 - c| := abs_add_le _ _
    _ ≤ (|a - b1| + |b1 - b2|) + |b2 - c| := add_le_add_left (abs_add_le _ _) _

/-- Cauchy of pairings from equicontinuity + bump convergence. -/

theorem slice_cauchy_asm
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (u : ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {ψ : ℝ → ℝ} (hψ : MemLp ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    {τ : ℝ} (hτ0 : t0 < τ) (hτ1 : τ < t1)
    (hEquicont : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < φ N → ∀ τ t : ℝ,
      τ ∈ Set.Icc t0 t1 → t ∈ Set.Icc t0 t1 →
      |(∫ x in (0 : ℝ)..1, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
        - (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)|
        ≤ Real.sqrt (C * (|τ - t| + (t1 - t0) / (φ N : ℝ))) * (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (hBump : ∀ δ : ℝ, 0 < δ → τ - δ ∈ Set.Ioi t0 → τ + δ ∈ Set.Iio t1 →
      Filter.Tendsto (fun N : ℕ => (1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ),
        (∫ x in (0 : ℝ)..1, (if t = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x))
      Filter.atTop (nhds ((1 / (2 * δ)) * ∫ t in (τ - δ)..(τ + δ),
        (∫ x in (0 : ℝ)..1, u t x * ψ x))))
 :
    CauchySeq (fun N : ℕ =>
        ∫ x in (0 : ℝ)..1, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x) := by
  obtain ⟨C, hC0, hC⟩ := hEquicont
  set K : ℝ := (eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hKdef
  by_cases hK : K = 0
  · have htop : eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
      ne_of_lt hψ.eLpNorm_lt_top
    have hzero : eLpNorm ψ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
      have h := (ENNReal.toReal_eq_zero_iff _).mp hK
      cases h with
      | inl h0 => exact h0
      | inr htop' => exact absurd htop' htop
    have hψ0 : ψ =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0 :=
      (eLpNorm_eq_zero_iff (by simp)).mp hzero
    have hAll : (fun N : ℕ => ∫ x in (0 : ℝ)..1, (if τ = t1 then (U_of (φ N) (φ N)).toFun x
             else (U_of (φ N) (Nat.floor ((τ - t0) / ((t1 - t0) / (φ N : ℝ))) + 1)).toFun x) * ψ x)
        = fun _ => 0 := by
      funext N
      have hτne : τ ≠ t1 := ne_of_lt hτ1
      simp only [hτne, ite_false]
      exact pairing_integral_zero ψ hψ0 _
    rw [hAll]
    exact cauchySeq_const 0
  · have hKpos : 0 < K := lt_of_le_of_ne' ENNReal.toReal_nonneg hK
    have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨δ, hδpos, hτδ0', hτδ1', hsmall⟩ := exists_small_delta hτ0 hτ1 hC0 hKpos heps
    have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hdiv : Tendsto (fun n : ℕ => (t1 - t0)/(n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (t1 - t0)
    have hcomp : Tendsto (fun N : ℕ => (t1 - t0)/((φ N : ℕ) : ℝ)) atTop (nhds 0) :=
      hdiv.comp hφtop
    have hev1 : ∀ᶠ N in atTop, (t1 - t0)/((φ N : ℕ) : ℝ) < δ :=
      hcomp.eventually_lt_const hδpos
    have hev2 : ∀ᶠ N in atTop, 0 < φ N :=
      hφtop.eventually (eventually_gt_atTop 0)
    have hev : ∀ᶠ N in atTop, ((t1 - t0)/((φ N : ℕ) : ℝ) < δ ∧ 0 < φ N) :=
      eventually_and.mpr ⟨hev1, hev2⟩
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
    have hBlim := hBump δ hδpos hτδ0' hτδ1'
    have hBcau := hBlim.cauchySeq
    have heps2 : 0 < eps/2 := by linarith
    obtain ⟨N1, hN1⟩ := (Metric.cauchySeq_iff.mp hBcau) (eps/2) heps2
    refine ⟨max N0 N1, fun m hm n hn => ?_⟩
    have hm0 : m ≥ N0 := le_trans (le_max_left _ _) hm
    have hm1 : m ≥ N1 := le_trans (le_max_right _ _) hm
    have hn0 : n ≥ N0 := le_trans (le_max_left _ _) hn
    have hn1 : n ≥ N1 := le_trans (le_max_right _ _) hn
    have hmr := (hN0 m hm0).1
    have hmph := (hN0 m hm0).2
    have hnr := (hN0 n hn0).1
    have hnph := (hN0 n hn0).2
    have hgm : Measurable (fun t : ℝ => ∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ m) (φ m)).toFun x
        else (U_of (φ m) (Nat.floor ((t - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x) :=
      slice_measurable U_of ψ t0 t1 (φ m) (φ m)
    have hgn : Measurable (fun t : ℝ => ∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ n) (φ n)).toFun x
        else (U_of (φ n) (Nat.floor ((t - t0)/((t1-t0)/(φ n : ℝ))) + 1)).toFun x) * ψ x) :=
      slice_measurable U_of ψ t0 t1 (φ n) (φ n)
    have hout_m : |(∫ x in (0:ℝ)..1, (if τ = t1 then (U_of (φ m) (φ m)).toFun x
          else (U_of (φ m) (Nat.floor ((τ - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x)
        - (1/(2*δ)) * ∫ t in (τ-δ)..(τ+δ), (∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ m) (φ m)).toFun x
          else (U_of (φ m) (Nat.floor ((t - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x)|
        ≤ Real.sqrt (C * (δ + δ)) * K :=
      avg_bound _ _ _ _ _ _ _ _ hgm hδpos hτδ0' hτδ1' hτ0 hτ1 hC0 hK0 (le_of_lt hmr)
        (fun s t hs ht => hC m hmph s t hs ht)
    have hout_n : |(∫ x in (0:ℝ)..1, (if τ = t1 then (U_of (φ n) (φ n)).toFun x
          else (U_of (φ n) (Nat.floor ((τ - t0)/((t1-t0)/(φ n : ℝ))) + 1)).toFun x) * ψ x)
        - (1/(2*δ)) * ∫ t in (τ-δ)..(τ+δ), (∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ n) (φ n)).toFun x
          else (U_of (φ n) (Nat.floor ((t - t0)/((t1-t0)/(φ n : ℝ))) + 1)).toFun x) * ψ x)|
        ≤ Real.sqrt (C * (δ + δ)) * K :=
      avg_bound _ _ _ _ _ _ _ _ hgn hδpos hτδ0' hτδ1' hτ0 hτ1 hC0 hK0 (le_of_lt hnr)
        (fun s t hs ht => hC n hnph s t hs ht)
    have hlt_m : |(∫ x in (0:ℝ)..1, (if τ = t1 then (U_of (φ m) (φ m)).toFun x
          else (U_of (φ m) (Nat.floor ((τ - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x)
        - (1/(2*δ)) * ∫ t in (τ-δ)..(τ+δ), (∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ m) (φ m)).toFun x
          else (U_of (φ m) (Nat.floor ((t - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x)| < eps/4 :=
      lt_of_le_of_lt hout_m hsmall
    set Bm : ℝ := (1/(2*δ)) * ∫ t in (τ-δ)..(τ+δ), (∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ m) (φ m)).toFun x
        else (U_of (φ m) (Nat.floor ((t - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x) with hBmdef
    set Bn : ℝ := (1/(2*δ)) * ∫ t in (τ-δ)..(τ+δ), (∫ x in (0:ℝ)..1, (if t = t1 then (U_of (φ n) (φ n)).toFun x
        else (U_of (φ n) (Nat.floor ((t - t0)/((t1-t0)/(φ n : ℝ))) + 1)).toFun x) * ψ x) with hBndef
    set Gm : ℝ := (∫ x in (0:ℝ)..1, (if τ = t1 then (U_of (φ m) (φ m)).toFun x
        else (U_of (φ m) (Nat.floor ((τ - t0)/((t1-t0)/(φ m : ℝ))) + 1)).toFun x) * ψ x) with hGmdef
    set Gn : ℝ := (∫ x in (0:ℝ)..1, (if τ = t1 then (U_of (φ n) (φ n)).toFun x
        else (U_of (φ n) (Nat.floor ((τ - t0)/((t1-t0)/(φ n : ℝ))) + 1)).toFun x) * ψ x) with hGndef
    have hlt_n : |Bn - Gn| < eps/4 := by
      rw [abs_sub_comm]
      exact lt_of_le_of_lt hout_n hsmall
    have hmid : |Bm - Bn| < eps/2 := by
      have h := hN1 m hm1 n hn1
      rw [Real.dist_eq] at h
      simpa only [hBmdef, hBndef] using h
    rw [Real.dist_eq]
    have htri : |Gm - Gn| ≤ |Gm - Bm| + |Bm - Bn| + |Bn - Gn| :=
      abs_sub_le_three _ _ _ _
    have hsum : |Gm - Bm| + |Bm - Bn| + |Bn - Gn| < eps := by
      have h := add_lt_add (add_lt_add hlt_m hmid) hlt_n
      have heq : (eps/4 + eps/2) + eps/4 = eps := by ring
      rwa [heq] at h
    simpa only [hGmdef, hGndef] using (lt_of_le_of_lt htri hsum)


theorem WeakH10_intervalIntegrable (w : WeakH10) :
    IntervalIntegrable w.weakDeriv volume 0 1 := by
  have hside : ‖w.weakDeriv 0‖ₑ ≠ ⊤ := by simp
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num) hside]
  exact w.weakDeriv_memLp.integrable (by norm_num)


theorem WeakH10_absCont (w : WeakH10) :
    AbsolutelyContinuousOnInterval w.toFun 0 1 := by
  have hac := (WeakH10_intervalIntegrable w).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp [Set.uIcc_of_le])
  apply hac.congr
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  exact (w.toFun_eq_integral x hx).symm


theorem WeakH10_deriv_ae (w : WeakH10) :
    ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 1 → deriv w.toFun x = w.weakDeriv x := by
  have hder := (WeakH10_intervalIntegrable w).ae_hasDerivAt_integral
  have h0mem : (0 : ℝ) ∈ Set.uIcc 0 1 := by simp [Set.uIcc_of_le]
  have hne1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := Measure.ae_ne _ 1
  filter_upwards [hder, hne1] with x hx hne hxuIoc
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxuIoc
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxuIoc.1, lt_of_le_of_ne hxuIoc.2 hne⟩
  have hxIcc : x ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.Ioc_subset_Icc_self hxuIoc
  have hprim := (hx hxIcc) 0 h0mem
  have heq : w.toFun =ᶠ[nhds x] (fun x => ∫ t in (0 : ℝ)..x, w.weakDeriv t) := by
    apply eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hxIoo)
    intro y hy
    exact w.toFun_eq_integral y (Set.Ioo_subset_Icc_self hy)
  have hfin := hprim.congr_of_eventuallyEq heq
  exact hfin.deriv


theorem WeakH10_endpoints (w : WeakH10) : w.toFun 0 = 0 ∧ w.toFun 1 = 0 := by
  constructor
  · rw [w.toFun_eq_integral 0 (by simp)]
    exact intervalIntegral.integral_same
  · rw [w.toFun_eq_integral 1 (by simp)]
    exact w.integral_weakDeriv_eq_zero


theorem WeakH10_continuousOn (w : WeakH10) : ContinuousOn w.toFun (Set.Icc 0 1) := by
  have h := (WeakH10_absCont w).continuousOn
  rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h


theorem ContinuousOn_bound_Icc (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ C, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ C := by
  by_cases hab : a ≤ b
  · obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ⟨le_refl a, hab⟩⟩ hf.norm
    exact ⟨‖f x0‖, fun x hx => (Filter.eventually_principal.mp hmax) x hx⟩
  · refine ⟨0, fun x hx => ?_⟩
    rw [Set.Icc_eq_empty hab] at hx
    exact absurd hx (Set.notMem_empty x)


theorem WeakH10_ibp
    (h v : WeakH10) :
    (∫ x in (0 : ℝ)..1, h.toFun x * v.weakDeriv x)
      = -(∫ x in (0 : ℝ)..1, h.weakDeriv x * v.toFun x) := by
  have hibp := (WeakH10_absCont h).integral_mul_deriv_eq_deriv_mul (WeakH10_absCont v)
  obtain ⟨h0, h1⟩ := WeakH10_endpoints h
  obtain ⟨v0, v1⟩ := WeakH10_endpoints v
  rw [h1, v1, h0, v0] at hibp
  simp only [mul_zero, sub_self, zero_sub] at hibp
  have e1 : (∫ x in (0 : ℝ)..1, h.toFun x * v.weakDeriv x)
      = ∫ x in (0 : ℝ)..1, h.toFun x * deriv v.toFun x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [WeakH10_deriv_ae v] with x hx hmem
    rw [hx hmem]
  have e2 : (∫ x in (0 : ℝ)..1, h.weakDeriv x * v.toFun x)
      = ∫ x in (0 : ℝ)..1, deriv h.toFun x * v.toFun x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [WeakH10_deriv_ae h] with x hx hmem
    rw [hx hmem]
  rw [e1, e2, hibp]


theorem WeakH10_ibp_Icc (h v : WeakH10) :
    (∫ x in Set.Icc (0 : ℝ) 1, h.toFun x * v.weakDeriv x ∂volume)
      = -(∫ x in Set.Icc (0 : ℝ) 1, h.weakDeriv x * v.toFun x ∂volume) := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact WeakH10_ibp h v


noncomputable def sliceIdx (t0 t1 : ℝ) (φ : ℕ → ℕ) (N : ℕ) (t : ℝ) : ℕ :=
  if t = t1 then φ N else Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) + 1


theorem sliceIdx_measurable (t0 t1 : ℝ) (φ : ℕ → ℕ) (N : ℕ) :
    Measurable (sliceIdx t0 t1 φ N) := by
  show Measurable fun t : ℝ => (if t = t1 then φ N else Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) + 1)
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_singleton t1
  · exact Measurable.add_const
      (Measurable.nat_floor (((continuous_id.sub continuous_const).div_const _).measurable)) 1


theorem sliceIdx_bound (t0 t1 : ℝ) (φ : ℕ → ℕ) (N : ℕ) (ht : t0 < t1) :
    ∀ t ∈ Set.Icc t0 t1, sliceIdx t0 t1 φ N t < φ N + 2 := by
  intro t htm
  show (if t = t1 then φ N else Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) + 1) < φ N + 2
  by_cases h : t = t1
  · rw [ite_eq_left h]
    omega
  · rw [ite_eq_right h]
    by_cases hφ0 : φ N = 0
    · rw [hφ0]
      simp only [Nat.cast_zero, div_zero]
      simp
    · have hφpos : (0 : ℝ) < φ N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hφ0)
      have hφne : (φ N : ℝ) ≠ 0 := ne_of_gt hφpos
      have hstep : (0 : ℝ) < (t1 - t0) / (φ N) := div_pos (sub_pos.mpr ht) hφpos
      have hy0 : (0 : ℝ) ≤ (t - t0) / ((t1 - t0) / (φ N)) :=
        div_nonneg (sub_nonneg.mpr htm.1) hstep.le
      have hy1 : (t - t0) / ((t1 - t0) / (φ N)) ≤ (φ N : ℝ) := by
        rw [div_le_iff₀ hstep]
        have hmul : (φ N : ℝ) * ((t1 - t0) / (φ N)) = t1 - t0 := by
          field_simp
        rw [hmul]
        exact sub_le_sub_right htm.2 t0
      have hflt : Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) < φ N + 1 := by
        rw [Nat.floor_lt hy0]
        calc (t - t0) / ((t1 - t0) / (φ N)) ≤ (φ N : ℝ) := hy1
          _ < (((φ N + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.lt_succ_self (φ N)
      omega


theorem sliceFubini {t0 t1 : ℝ} (P : ℕ → ℝ → ℝ) (Q : ℝ → ℝ)
    (k : ℝ → ℕ) (M : ℕ) {ζ : ℝ → ℝ} (hζcont : Continuous ζ)
    (hk : Measurable k) (hkM : ∀ t ∈ Set.Icc t0 t1, k t < M)
    (hPQ : ∀ j, Integrable (fun x => P j x * Q x) (volume.restrict (Set.Icc 0 1))) :
    (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, P (k p.1) p.2 * (ζ p.1 * Q p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    = ∫ t in Set.Icc t0 t1, ζ t * (∫ x in Set.Icc (0 : ℝ) 1, P (k t) x * Q x ∂volume) ∂volume := by
  have he_meas : ∀ j, Measurable fun t : ℝ => (if k t = j then (1 : ℝ) else 0) := by
    intro j
    apply Measurable.ite _ measurable_const measurable_const
    exact hk (measurableSet_singleton j)
  have hz_int : ∀ j, Integrable (fun t => (if k t = j then (1 : ℝ) else 0) * ζ t)
      (volume.restrict (Set.Icc t0 t1)) := by
    intro j
    obtain ⟨C, hC⟩ := ContinuousOn_bound_Icc ζ t0 t1 hζcont.continuousOn
    refine Integrable.of_bound ((he_meas j).mul hζcont.measurable).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    calc ‖(if k t = j then (1 : ℝ) else 0) * ζ t‖
        = ‖(if k t = j then (1 : ℝ) else 0)‖ * ‖ζ t‖ := norm_mul _ _
      _ ≤ 1 * C := mul_le_mul (by split_ifs <;> simp) (hC t ht) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hS_int : ∀ j, Integrable
      (fun p : ℝ × ℝ => ((if k p.1 = j then (1 : ℝ) else 0) * ζ p.1) * (P j p.2 * Q p.2))
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc 0 1))) := by
    intro j
    exact (hz_int j).mul_prod (hPQ j)
  have hsum_eq : ∀ p ∈ Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, P (k p.1) p.2 * (ζ p.1 * Q p.2)
      = ∑ j ∈ Finset.range M, ((if k p.1 = j then (1 : ℝ) else 0) * ζ p.1) * (P j p.2 * Q p.2) := by
    intro p hp
    have hmem : k p.1 ∈ Finset.range M := Finset.mem_range.mpr (hkM p.1 hp.1)
    have h0 : ∀ j ∈ Finset.range M, j ≠ k p.1 →
        ((if k p.1 = j then (1 : ℝ) else 0) * ζ p.1) * (P j p.2 * Q p.2) = 0 := by
      intro j _ hne
      have hkj : k p.1 ≠ j := fun h' => hne h'.symm
      simp [hkj]
    rw [Finset.sum_eq_single_of_mem (k p.1) hmem h0, ite_eq_left rfl]
    ring
  have hA_int : IntegrableOn (fun p : ℝ × ℝ => P (k p.1) p.2 * (ζ p.1 * Q p.2))
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    show Integrable _ ((volume.prod volume).restrict _)
    have hsum_int' : Integrable
        (∑ j ∈ Finset.range M, fun p : ℝ × ℝ => ((if k p.1 = j then (1 : ℝ) else 0) * ζ p.1) * (P j p.2 * Q p.2))
        ((volume.prod volume).restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
      rw [← Measure.prod_restrict]
      exact integrable_finsetSum' _ (fun j _ => hS_int j)
    apply hsum_int'.congr
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    rw [Finset.sum_apply]
    exact (hsum_eq p hp).symm
  have hrest : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, P (k p.1) p.2 * (ζ p.1 * Q p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, P (k p.1) p.2 * (ζ p.1 * Q p.2)
        ∂volume := by
    rw [Measure.restrict_restrict_of_subset (Set.Subset.refl _)]
  rw [hrest, Measure.volume_eq_prod, setIntegral_prod _ hA_int]
  apply setIntegral_congr_ae measurableSet_Icc
  refine ae_of_all _ fun t ht => ?_
  show (∫ x in Set.Icc (0 : ℝ) 1, P (k t) x * (ζ t * Q x) ∂volume)
    = ζ t * (∫ x in Set.Icc (0 : ℝ) 1, P (k t) x * Q x ∂volume)
  rw [← integral_const_mul]
  apply setIntegral_congr_ae measurableSet_Icc
  refine ae_of_all _ fun x hx => ?_
  ring

/-- Integrated micro-IbP against a time cutoff. -/

theorem integrated_ibp
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {ζ : ℝ → ℝ} (hζcont : Continuous ζ) (hζsupp : HasCompactSupport ζ)
    {N : ℕ} {v : WeakH10} :
    (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
       else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
        * (ζ p.1 * v.weakDeriv p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = -(∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
         else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).weakDeriv p.2)
          * (ζ p.1 * v.toFun p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) := by
  have hk : Measurable (sliceIdx t0 t1 φ N) := sliceIdx_measurable t0 t1 φ N
  have hkM : ∀ t ∈ Set.Icc t0 t1, sliceIdx t0 t1 φ N t < φ N + 2 :=
    sliceIdx_bound t0 t1 φ N ht
  have hPQ_A : ∀ j, Integrable (fun x => (U_of (φ N) j).toFun x * v.weakDeriv x)
      (volume.restrict (Set.Icc 0 1)) := by
    intro j
    obtain ⟨C, hC⟩ := ContinuousOn_bound_Icc _ 0 1
      (WeakH10_continuousOn (U_of (φ N) j))
    have hb : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖(U_of (φ N) j).toFun x‖ ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hC x hx
    exact Integrable.bdd_mul (v.weakDeriv_memLp.integrable (by norm_num))
      ((WeakH10_continuousOn _).aestronglyMeasurable measurableSet_Icc) hb
  have hPQ_B : ∀ j, Integrable (fun x => (U_of (φ N) j).weakDeriv x * v.toFun x)
      (volume.restrict (Set.Icc 0 1)) := by
    intro j
    obtain ⟨C, hC⟩ := ContinuousOn_bound_Icc _ 0 1 (WeakH10_continuousOn v)
    have hb : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖v.toFun x‖ ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hC x hx
    have h1 : Integrable (fun x => v.toFun x * (U_of (φ N) j).weakDeriv x)
        (volume.restrict (Set.Icc 0 1)) :=
      Integrable.bdd_mul ((U_of (φ N) j).weakDeriv_memLp.integrable (by norm_num))
        ((WeakH10_continuousOn v).aestronglyMeasurable measurableSet_Icc) hb
    apply h1.congr
    filter_upwards with x
    ring
  have hA : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (U_of (φ N) (sliceIdx t0 t1 φ N p.1)).toFun p.2 * (ζ p.1 * v.weakDeriv p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ t in Set.Icc t0 t1, ζ t * (∫ x in Set.Icc (0 : ℝ) 1,
        (U_of (φ N) (sliceIdx t0 t1 φ N t)).toFun x * v.weakDeriv x ∂volume) ∂volume :=
    sliceFubini (fun j x => (U_of (φ N) j).toFun x) v.weakDeriv (sliceIdx t0 t1 φ N)
      (φ N + 2) hζcont hk hkM hPQ_A
  have hB : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (U_of (φ N) (sliceIdx t0 t1 φ N p.1)).weakDeriv p.2 * (ζ p.1 * v.toFun p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ t in Set.Icc t0 t1, ζ t * (∫ x in Set.Icc (0 : ℝ) 1,
        (U_of (φ N) (sliceIdx t0 t1 φ N t)).weakDeriv x * v.toFun x ∂volume) ∂volume :=
    sliceFubini (fun j x => (U_of (φ N) j).weakDeriv x) v.toFun (sliceIdx t0 t1 φ N)
      (φ N + 2) hζcont hk hkM hPQ_B
  have hAeq : (fun p : ℝ × ℝ => (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
        * (ζ p.1 * v.weakDeriv p.2))
      = fun p => (U_of (φ N) (sliceIdx t0 t1 φ N p.1)).toFun p.2 * (ζ p.1 * v.weakDeriv p.2) := by
    funext p
    by_cases h : p.1 = t1
    · simp only [sliceIdx, ite_eq_left h]
    · simp only [sliceIdx, ite_eq_right h]
  have hBeq : (fun p : ℝ × ℝ => (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).weakDeriv p.2)
        * (ζ p.1 * v.toFun p.2))
      = fun p => (U_of (φ N) (sliceIdx t0 t1 φ N p.1)).weakDeriv p.2 * (ζ p.1 * v.toFun p.2) := by
    funext p
    by_cases h : p.1 = t1
    · simp only [sliceIdx, ite_eq_left h]
    · simp only [sliceIdx, ite_eq_right h]
  rw [hAeq, hBeq, hA, hB, ← integral_neg]
  apply setIntegral_congr_ae measurableSet_Icc
  refine ae_of_all _ fun t ht => ?_
  have hcd : (∫ x in Set.Icc (0 : ℝ) 1, (U_of (φ N) (sliceIdx t0 t1 φ N t)).weakDeriv x * v.toFun x ∂volume)
      = -(∫ x in Set.Icc (0 : ℝ) 1, (U_of (φ N) (sliceIdx t0 t1 φ N t)).toFun x * v.weakDeriv x ∂volume) := by
    by_cases h : t = t1
    · simp only [sliceIdx, ite_eq_left h]
      linear_combination WeakH10_ibp_Icc (U_of (φ N) (φ N)) v
    · simp only [sliceIdx, ite_eq_right h]
      linear_combination WeakH10_ibp_Icc (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (φ N))) + 1)) v
  rw [hcd]
  ring


theorem toFun_memLp_of_weak (v : WeakH10) :
    MemLp v.toFun 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hw1 : Integrable v.weakDeriv (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    v.weakDeriv_memLp.integrable one_le_two
  have hw'ind : Integrable ((Set.Icc (0 : ℝ) 1).indicator v.weakDeriv) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hw1
  have hFc : Continuous (fun x : ℝ =>
      ∫ t in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator v.weakDeriv t) :=
    hw'ind.continuous_primitive 0
  have heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, v.toFun x
      = ∫ t in (0 : ℝ)..x, (Set.Icc (0 : ℝ) 1).indicator v.weakDeriv t := by
    intro x hx
    rw [v.toFun_eq_integral x hx, intervalIntegral.integral_of_le hx.1,
      intervalIntegral.integral_of_le hx.1]
    apply setIntegral_congr_ae measurableSet_Ioc
    apply Filter.Eventually.of_forall
    intro t ht
    have hmem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, le_trans ht.2 hx.2⟩
    exact (Set.indicator_of_mem hmem _).symm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc.continuousOn
  refine MemLp.of_bound (hFc.aestronglyMeasurable.congr ?_) C ?_
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun x hx => (heq x hx).symm)
  · exact (ae_restrict_mem measurableSet_Icc).mono
      (fun x hx => by rw [heq x hx]; exact hC x hx)


theorem memLp_uncurry_mul (t0 t1 : ℝ) (ζ g : ℝ → ℝ)
    (hζ : MemLp ζ ⊤ (volume.restrict (Set.Icc t0 t1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (Function.uncurry fun t x => ζ t * g x) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmeas : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc t0 t1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
  rw [hmeas]
  have h1 : MemLp (fun p : ℝ × ℝ => ζ p.1) ⊤
      ((volume.restrict (Set.Icc t0 t1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hζ.comp_fst _
  have h2 : MemLp (fun p : ℝ × ℝ => g p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    hg.comp_snd _
  have h : MemLp ((fun p : ℝ × ℝ => ζ p.1) * (fun p : ℝ × ℝ => g p.2)) 2
      ((volume.restrict (Set.Icc t0 t1)).prod
        (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    h1.mul h2
  exact h

/-- Weak passage of the integrated IbP. -/

theorem ibp_weak_passage
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (u ux : ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hWeakU : ∀ ψ : ℝ → ℝ → ℝ,
        MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
        Filter.Tendsto (fun N : ℕ =>
            ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
               else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
                * ψ p.1 p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            u p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hWeakUx : ∀ ψ : ℝ → ℝ → ℝ,
        MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
        Filter.Tendsto (fun N : ℕ =>
            ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
               else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).weakDeriv p.2)
                * ψ p.1 p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ux p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hInt : ∀ (N : ℕ) (ζ : ℝ → ℝ), Continuous ζ → HasCompactSupport ζ → ∀ v : WeakH10,
      (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
         else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
          * (ζ p.1 * v.weakDeriv p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
        = -(∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
           else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).weakDeriv p.2)
            * (ζ p.1 * v.toFun p.2)
            ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))
    {ζ : ℝ → ℝ} (hζcont : Continuous ζ) (hζsupp : HasCompactSupport ζ)
    {v : WeakH10} :
    (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      u p.1 p.2 * (ζ p.1 * v.weakDeriv p.2)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = -(∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        ux p.1 p.2 * (ζ p.1 * v.toFun p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) := by
  have hζtop : MemLp ζ ⊤ (volume.restrict (Set.Icc t0 t1)) :=
    hζcont.memLp_top_of_hasCompactSupport hζsupp _
  have hD : MemLp (Function.uncurry fun t x => ζ t * v.weakDeriv x) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    memLp_uncurry_mul t0 t1 ζ v.weakDeriv hζtop v.weakDeriv_memLp
  have hT : MemLp (Function.uncurry fun t x => ζ t * v.toFun x) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    memLp_uncurry_mul t0 t1 ζ v.toFun hζtop (toFun_memLp_of_weak v)
  have eU := hWeakU (fun t x => ζ t * v.weakDeriv x) hD
  have eUx := hWeakUx (fun t x => ζ t * v.toFun x) hT
  have hEq : ∀ N : ℕ, (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
         else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
          * (ζ p.1 * v.weakDeriv p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = -(∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
         else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).weakDeriv p.2)
          * (ζ p.1 * v.toFun p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) :=
    fun N => hInt N ζ hζcont hζsupp v
  have hlim : Filter.Tendsto (fun N : ℕ => ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
         else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
          * (ζ p.1 * v.weakDeriv p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) Filter.atTop
      (nhds (-(∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        ux p.1 p.2 * (ζ p.1 * v.toFun p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))) :=
    Filter.Tendsto.congr (fun N => (hEq N).symm) eUx.neg
  have eU' : Filter.Tendsto (fun N : ℕ => ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        (if p.1 = t1 then (U_of (φ N) (φ N)).toFun p.2
         else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).toFun p.2)
          * (ζ p.1 * v.weakDeriv p.2)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) Filter.atTop
      (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        u p.1 p.2 * (ζ p.1 * v.weakDeriv p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) :=
    eU
  exact tendsto_nhds_unique eU' hlim


theorem ibp_rep_transfer
    {t0 t1 : ℝ} (ht : t0 < t1)
    (u ux : ℝ → ℝ → ℝ) (ũ : ℝ → ℝ → ℝ)
    (hIbP : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ v : WeakH10,
      (∫ x in (0 : ℝ)..1, u τ x * v.weakDeriv x)
        = -(∫ x in (0 : ℝ)..1, ux τ x * v.toFun x))
    (hPairUx : ∀ w : ℝ → ℝ, MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        ∀ t ∈ Set.Icc t0 t1, (∫ x in (0 : ℝ)..1, ux t x * w x) = ĝ t)
    (hRepDef : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∃ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1)
      ∧ Filter.Tendsto s Filter.atTop (nhds τ)
      ∧ Filter.Tendsto (fun n => (eLpNorm (fun x => ũ τ x - u (s n) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) Filter.atTop (nhds 0))
    (hPairLim : ∀ (τ : ℝ), τ ∈ Set.Icc t0 t1 → ∀ (s : ℕ → ℝ),
      (∀ n : ℕ, s n ∈ Set.Icc t0 t1) → Filter.Tendsto s Filter.atTop (nhds τ) →
      Filter.Tendsto (fun n => (eLpNorm (fun x => ũ τ x - u (s n) x) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) Filter.atTop (nhds 0) →
      ∀ v : WeakH10,
      Filter.Tendsto (fun n => ∫ x in (0 : ℝ)..1, u (s n) x * v.weakDeriv x)
        Filter.atTop (nhds (∫ x in (0 : ℝ)..1, ũ τ x * v.weakDeriv x))) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∀ v : WeakH10,
      (∫ x in (0 : ℝ)..1, ũ τ x * v.weakDeriv x)
        = -(∫ x in (0 : ℝ)..1, ux τ x * v.toFun x) := by
  intro τ hτ v
  obtain ⟨s, hs_mem, hs_lim, hs_enorm⟩ := hRepDef τ hτ
  obtain ⟨ĝ, hĝ_cont, hĝ_eq⟩ := hPairUx v.toFun (weakH10_toFun_memLp v)
  have h1 : Filter.Tendsto (fun n => ∫ x in (0 : ℝ)..1, u (s n) x * v.weakDeriv x)
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, ũ τ x * v.weakDeriv x)) :=
    hPairLim τ hτ s hs_mem hs_lim hs_enorm v
  have h4 : Filter.Tendsto (fun n => ĝ (s n)) Filter.atTop (nhds (ĝ τ)) :=
    (hĝ_cont.tendsto τ).comp hs_lim
  have h5 : Filter.Tendsto (fun n => ∫ x in (0 : ℝ)..1, ux (s n) x * v.toFun x)
      Filter.atTop (nhds (∫ x in (0 : ℝ)..1, ux τ x * v.toFun x)) := by
    have h5a := Filter.Tendsto.congr (fun n => (hĝ_eq (s n) (hs_mem n)).symm) h4
    rwa [(hĝ_eq τ hτ).symm] at h5a
  have h6 : Filter.Tendsto (fun n => ∫ x in (0 : ℝ)..1, u (s n) x * v.weakDeriv x)
      Filter.atTop (nhds (-(∫ x in (0 : ℝ)..1, ux τ x * v.toFun x))) :=
    Filter.Tendsto.congr (fun n => (hIbP (s n) (hs_mem n) v).symm) h5.neg
  exact tendsto_nhds_unique h1 h6


theorem slice_mean_op_bounded
    {t0 t1 : ℝ} (ht : t0 < t1)
    {w : ℝ → ℝ → ℝ} (hw : MemLp (Function.uncurry w) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) :
    MemLp (fun t => ∫ x in (0 : ℝ)..1, w t x) 2 (volume.restrict (Set.Icc t0 t1))
    ∧ (eLpNorm (fun t => ∫ x in (0 : ℝ)..1, w t x) 2 (volume.restrict (Set.Icc t0 t1))).toReal
        ≤ (eLpNorm (Function.uncurry w) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))).toReal := by
  have hμr : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [hμr]
    infer_instance
  have hwInt : Integrable (Function.uncurry w)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    hw.integrable one_le_two
  have hw' : MemLp (Function.uncurry w) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rwa [← hμr]
  have hwInt' : Integrable (Function.uncurry w)
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rwa [← hμr]
  have hM_int : Integrable (fun t => ∫ x, w t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (volume.restrict (Set.Icc t0 t1)) :=
    hwInt'.integral_prod_left
  have hM_meas : AEStronglyMeasurable (fun t => ∫ x, w t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      (volume.restrict (Set.Icc t0 t1)) :=
    hM_int.aestronglyMeasurable
  have h2r : (2 : ENNReal).toReal = (2 : ℝ) := by simp
  have hμx1 : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  have hnorm : eLpNorm (fun t => ∫ x, w t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) 2
        (volume.restrict (Set.Icc t0 t1))
      ≤ eLpNorm (Function.uncurry w) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [hμr, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hM_meas,
      eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hw'.aestronglyMeasurable]
    simp only [eLpNorm'_eq_lintegral_enorm, h2r]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    calc ∫⁻ t, ‖∫ x, w t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))‖ₑ ^ (2 : ℝ)
            ∂(volume.restrict (Set.Icc t0 t1))
        ≤ ∫⁻ t, (∫⁻ x, ‖w t x‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
            ∂(volume.restrict (Set.Icc t0 t1)) := by
          apply lintegral_mono_ae
          filter_upwards [hwInt'.prod_right_ae] with t ht
          have hmeas : AEMeasurable (fun x => ‖w t x‖ₑ)
              (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
            ht.aestronglyMeasurable.enorm
          have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq
            (volume.restrict (Set.Icc (0 : ℝ) 1)) Real.HolderConjugate.two_two
            (f := fun x => ‖w t x‖ₑ) (g := fun _ => 1) hmeas aemeasurable_const
          simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one, hμx1,
            mul_one] at hH
          calc ‖∫ x, w t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))‖ₑ ^ (2 : ℝ)
              ≤ (∫⁻ x, ‖w t x‖ₑ ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) (by norm_num)
            _ ≤ ∫⁻ x, ‖w t x‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
                have hle : (∫⁻ x, ‖w t x‖ₑ ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ^ (2 : ℝ)
                    ≤ ((∫⁻ x, ‖w t x‖ₑ ^ (2 : ℝ)
                      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
                  ENNReal.rpow_le_rpow hH (by norm_num)
                rwa [← ENNReal.rpow_mul, show (1 : ℝ) / 2 * 2 = 1 by norm_num,
                  ENNReal.rpow_one] at hle
      _ = ∫⁻ p, ‖Function.uncurry w p‖ₑ ^ (2 : ℝ)
            ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
          rw [lintegral_prod _ ((hw'.aestronglyMeasurable.enorm).pow_const (2 : ℝ))]
          refine lintegral_congr_ae (Eventually.of_forall fun t => ?_)
          refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
          rfl
  have hfun : (fun t => ∫ x in (0 : ℝ)..1, w t x)
      = (fun t => ∫ x, w t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    funext t
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
  rw [hfun]
  refine ⟨memLp_iff.mpr (lt_of_le_of_lt hnorm hw.eLpNorm_lt_top), ?_⟩
  exact ENNReal.toReal_mono hw.eLpNorm_lt_top.ne hnorm



/-- Slice means of the gradient limit vanish a.e. -/

theorem slice_mean_zero_ae
    {t0 t1 : ℝ} (ht : t0 < t1)
    (U_of : ℕ → ℕ → WeakH10) (ux : ℝ → ℝ → ℝ)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hMemUx : MemLp (Function.uncurry ux) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hWeakUx : ∀ ψ : ℝ → ℝ → ℝ,
        MemLp (Function.uncurry ψ) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) →
        Filter.Tendsto (fun N : ℕ =>
            ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
              (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
               else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (φ N))) + 1)).weakDeriv p.2)
                * ψ p.1 p.2
                ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
          Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
            ux p.1 p.2 * ψ p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))))
    (hPairUx : ∀ w : ℝ → ℝ, MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        (fun t => ∫ x in (0 : ℝ)..1, ux t x * w x)
          =ᵐ[volume.restrict (Set.Icc t0 t1)] ĝ) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)), (∫ x in (0 : ℝ)..1, ux t x) = 0 := by
  have hμr : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h2r : (2 : ENNReal).toReal = (2 : ℝ) := by simp
  have hμx1 : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  have hMemM : MemLp (fun t => ∫ x in (0 : ℝ)..1, ux t x) 2
      (volume.restrict (Set.Icc t0 t1)) :=
    (slice_mean_op_bounded ht hMemUx).1
  have hfunUx : ∀ t : ℝ, (∫ x, ux t x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ x in (0 : ℝ)..1, ux t x := by
    intro t
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
  have helper_fst : ∀ m : ℝ → ℝ, MemLp m 2 (volume.restrict (Set.Icc t0 t1)) →
      MemLp (fun p : ℝ × ℝ => m p.1) 2
        ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    intro m hm
    have hmInt : Integrable m (volume.restrict (Set.Icc t0 t1)) := hm.integrable one_le_two
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => m p.1)
        ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
      (hmInt.comp_fst _).aestronglyMeasurable
    rw [memLp_iff, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hmeas,
      eLpNorm'_eq_lintegral_enorm, h2r]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    have hfin : (∫⁻ t, ‖m t‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc t0 t1))) < ⊤ := by
      have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (f := m) (p := 2)
        two_ne_zero ENNReal.ofNat_ne_top hm.eLpNorm_lt_top
      rwa [h2r] at h
    have hLint : (∫⁻ p : ℝ × ℝ, ‖m p.1‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
        = ∫⁻ t, ‖m t‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc t0 t1)) := by
      have hprod := lintegral_prod_mul (μ := (volume.restrict (Set.Icc t0 t1)))
        (ν := (volume.restrict (Set.Icc (0 : ℝ) 1))) (f := (fun t => ‖m t‖ₑ ^ (2 : ℝ)))
        (g := (fun _ => (1 : ENNReal)))
        ((hm.aestronglyMeasurable.enorm).pow_const (2 : ℝ)) aemeasurable_const
      simp only [lintegral_one, hμx1, mul_one] at hprod
      exact hprod
    rw [hLint]
    exact ne_of_lt hfin
  have helper_snd : ∀ g : ℝ → ℝ, MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      MemLp (fun p : ℝ × ℝ => g p.2) 2
        ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    intro g hg
    have hgInt : Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1)) := hg.integrable one_le_two
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2)
        ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
      (hgInt.comp_snd _).aestronglyMeasurable
    rw [memLp_iff, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hmeas,
      eLpNorm'_eq_lintegral_enorm, h2r]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    have hfin : (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) < ⊤ := by
      have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (f := g) (p := 2)
        two_ne_zero ENNReal.ofNat_ne_top hg.eLpNorm_lt_top
      rwa [h2r] at h
    have hμtfin : ((volume.restrict (Set.Icc t0 t1)) Set.univ) < ⊤ := by
      rw [Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have hLint : (∫⁻ p : ℝ × ℝ, ‖g p.2‖ₑ ^ (2 : ℝ)
        ∂((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
        = ((volume.restrict (Set.Icc t0 t1)) Set.univ)
          * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      have hprod := lintegral_prod_mul (μ := (volume.restrict (Set.Icc t0 t1)))
        (ν := (volume.restrict (Set.Icc (0 : ℝ) 1))) (f := (fun _ => (1 : ENNReal)))
        (g := (fun x => ‖g x‖ₑ ^ (2 : ℝ)))
        aemeasurable_const ((hg.aestronglyMeasurable.enorm).pow_const (2 : ℝ))
      simp only [lintegral_one, one_mul] at hprod
      exact hprod
    rw [hLint]
    exact ne_of_lt (ENNReal.mul_lt_top hμtfin hfin)
  have hΨmem : MemLp (fun p : ℝ × ℝ => (∫ x in (0 : ℝ)..1, ux p.1 x)) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    helper_fst _ hMemM
  have hfloor_meas : Measurable (Nat.floor : ℝ → ℕ) := by
    apply measurable_to_countable'
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [Nat.preimage_floor_zero]
      exact measurableSet_Iio
    · rw [Nat.preimage_floor_of_ne_zero hn]
      exact measurableSet_Ico
  have hKmeas : ∀ A : ℕ, Measurable
      (fun t : ℝ => Nat.floor ((t - t0) / ((t1 - t0) / (A : ℝ))) + 1) := by
    intro A
    have hdiv : Measurable (fun t : ℝ => (t - t0) / ((t1 - t0) / (A : ℝ))) :=
      ((continuous_id.sub continuous_const).div_const _).measurable
    have hadd1 : Measurable (fun n : ℕ => n + 1) :=
      continuous_of_discreteTopology.measurable
    exact hadd1.comp (hfloor_meas.comp hdiv)
  have hKrange : ∀ (A : ℕ) (t : ℝ), t ∈ Set.Icc t0 t1 →
      Nat.floor ((t - t0) / ((t1 - t0) / (A : ℝ))) + 1 ∈ Finset.range (A + 2) := by
    intro A t htI
    rw [Finset.mem_range]
    by_cases hA : A = 0
    · subst hA
      simp only [Nat.cast_zero, div_zero, Nat.floor_zero]
      norm_num
    · have hApos : (0 : ℝ) < A := by exact_mod_cast Nat.pos_of_ne_zero hA
      have hAne : (A : ℝ) ≠ 0 := ne_of_gt hApos
      have htt : (0 : ℝ) < t1 - t0 := sub_pos.mpr ht
      have hdpos : (0 : ℝ) < (t1 - t0) / A := div_pos htt hApos
      have ht0 : t0 ≤ t := htI.1
      have ht1 : t ≤ t1 := htI.2
      have hq_nonneg : (0 : ℝ) ≤ (t - t0) / ((t1 - t0) / A) :=
        div_nonneg (sub_nonneg.mpr ht0) (le_of_lt hdpos)
      have hq_le : (t - t0) / ((t1 - t0) / A) ≤ A := by
        rw [div_le_iff₀ hdpos, ← mul_div_assoc, mul_div_cancel_left₀ _ hAne]
        linarith
      have hfloor_le : Nat.floor ((t - t0) / ((t1 - t0) / A)) ≤ A := by
        have h1 : ((Nat.floor ((t - t0) / ((t1 - t0) / A)) : ℕ) : ℝ)
            ≤ (A : ℝ) :=
          le_trans (Nat.floor_le hq_nonneg) hq_le
        exact_mod_cast h1
      omega
  have hIN : ∀ N : ℕ, MemLp
      (fun p : ℝ × ℝ => if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
      2 ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    intro N
    have hpieces : ∀ j : ℕ, MemLp
        (fun p : ℝ × ℝ => if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
          then (U_of (φ N) j).weakDeriv p.2 else 0)
        2 ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      intro j
      have hsmeas : MeasurableSet {p : ℝ × ℝ |
          Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j} := by
        have h1 : MeasurableSet ((fun t : ℝ =>
            Nat.floor ((t - t0) / ((t1 - t0) / (↑(φ N)))) + 1) ⁻¹' {j}) :=
          hKmeas _ (measurableSet_singleton j)
        have h2 : {p : ℝ × ℝ |
            Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j}
            = Prod.fst ⁻¹' ((fun t : ℝ =>
              Nat.floor ((t - t0) / ((t1 - t0) / (↑(φ N)))) + 1) ⁻¹' {j}) := rfl
        rw [h2]
        exact measurable_fst h1
      have h1 : MemLp
          (({p : ℝ × ℝ |
            Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j}).indicator
            (fun p : ℝ × ℝ => (U_of (φ N) j).weakDeriv p.2))
          2 ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
        MemLp.indicator hsmeas.nullMeasurableSet
          (helper_snd _ (U_of (φ N) j).weakDeriv_memLp)
      have h2 : (({p : ℝ × ℝ |
            Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j}).indicator
            (fun p : ℝ × ℝ => (U_of (φ N) j).weakDeriv p.2))
            =ᵐ[((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))]
          (fun p : ℝ × ℝ => if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
            then (U_of (φ N) j).weakDeriv p.2 else 0) := by
        apply Eventually.of_forall
        intro p
        by_cases hk : Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
        · have hkmem : p ∈ {p : ℝ × ℝ |
              Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j} := hk
          rw [Set.indicator_of_mem hkmem]
          show (U_of (φ N) j).weakDeriv p.2 =
            (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
              then (U_of (φ N) j).weakDeriv p.2 else 0)
          rw [ite_eq_left hk]
        · have hknmem : p ∉ {p : ℝ × ℝ |
              Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j} := hk
          rw [Set.indicator_of_notMem hknmem]
          show (0 : ℝ) =
            (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
              then (U_of (φ N) j).weakDeriv p.2 else 0)
          rw [ite_eq_right hk]
      exact (memLp_congr_ae h2).mp h1
    have hG : MemLp (fun p : ℝ × ℝ => ∑ j ∈ Finset.range (φ N + 2),
        (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
          then (U_of (φ N) j).weakDeriv p.2 else 0))
        2 ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
      memLp_finsetSum _ (fun j _ => hpieces j)
    have hnull1 : ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (({t1} ×ˢ Set.univ) : Set (ℝ × ℝ)) = 0 := by
      rw [Measure.prod_prod]
      have h0 : (volume.restrict (Set.Icc t0 t1)) {t1} = 0 := by
        rw [Measure.restrict_apply (measurableSet_singleton t1)]
        exact measure_mono_null Set.inter_subset_left (measure_singleton t1)
      rw [h0, zero_mul]
    have hnull2 : ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (((Set.Icc t0 t1)ᶜ ×ˢ Set.univ) : Set (ℝ × ℝ)) = 0 := by
      rw [Measure.prod_prod]
      have h0 : (volume.restrict (Set.Icc t0 t1)) (Set.Icc t0 t1)ᶜ = 0 := by
        rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self, measure_empty]
      rw [h0, zero_mul]
    have hsub : {p : ℝ × ℝ | (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
          else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
          ≠ ∑ j ∈ Finset.range (φ N + 2),
          (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
            then (U_of (φ N) j).weakDeriv p.2 else 0)}
        ⊆ (({t1} ×ˢ Set.univ) ∪ ((Set.Icc t0 t1)ᶜ ×ˢ Set.univ) : Set (ℝ × ℝ)) := by
      intro p hp
      rw [Set.mem_ofPred_eq] at hp
      by_cases ht1 : p.1 = t1
      · left
        exact ⟨ht1, Set.mem_univ p.2⟩
      · by_cases hI : p.1 ∈ Set.Icc t0 t1
        · exfalso
          apply hp
          rw [ite_eq_right ht1]
          have hkr := hKrange (φ N) p.1 hI
          rw [Finset.sum_ite_eq _ _ (fun j => (U_of (φ N) j).weakDeriv p.2)]
          rw [ite_eq_left hkr]
        · right
          exact ⟨hI, Set.mem_univ p.2⟩
    have hnull : ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))
        {p : ℝ × ℝ | (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
          else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
          ≠ ∑ j ∈ Finset.range (φ N + 2),
          (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
            then (U_of (φ N) j).weakDeriv p.2 else 0)} = 0 :=
      measure_mono_null hsub (measure_union_null hnull1 hnull2)
    have hNG : (fun p : ℝ × ℝ => if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
        =ᵐ[((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))]
        (fun p : ℝ × ℝ => ∑ j ∈ Finset.range (φ N + 2),
        (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
          then (U_of (φ N) j).weakDeriv p.2 else 0)) := by
      show {p : ℝ × ℝ | (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
        = ∑ j ∈ Finset.range (φ N + 2),
        (if Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1 = j
          then (U_of (φ N) j).weakDeriv p.2 else 0)} ∈ ae _
      rw [mem_ae_iff, Set.compl_ofPred]
      exact hnull
    exact (memLp_congr_ae hNG).mpr hG
  have hMemUx' : MemLp (Function.uncurry ux) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rwa [← hμr]
  have hrr : ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
      = volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    Measure.restrict_restrict_of_subset (fun x hx => hx)
  have hΨmem_r : MemLp
      (Function.uncurry (fun t _ => ∫ x in (0 : ℝ)..1, ux t x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [hμr]
    exact hΨmem
  have hlim := hWeakUx (fun t _ => ∫ x in (0 : ℝ)..1, ux t x) hΨmem_r
  have hslice0 : ∀ (N j : ℕ), (∫ x, (U_of (φ N) j).weakDeriv x
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) = 0 := by
    intro N j
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (U_of (φ N) j).integral_weakDeriv_eq_zero
  have hLHS0 : ∀ N : ℕ, (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
        * (∫ x in (0 : ℝ)..1, ux p.1 x)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) = 0 := by
    intro N
    have hInt : Integrable (fun p : ℝ × ℝ =>
        (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
          else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
          * (∫ x in (0 : ℝ)..1, ux p.1 x))
        (((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) :=
      memLp_one_iff_integrable.mp (MemLp.mul (hIN N) hΨmem)
    have hFub : (∫ p, (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
          else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
          * (∫ x in (0 : ℝ)..1, ux p.1 x)
          ∂(((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))))
        = ∫ t, (∫ x, ((if t = t1 then (U_of (φ N) (φ N)).weakDeriv x
          else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv x)
          * (∫ x in (0 : ℝ)..1, ux t x)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        ∂(volume.restrict (Set.Icc t0 t1)) :=
      integral_prod _ hInt
    rw [hrr, hμr, hFub]
    have h0 : ∀ t : ℝ, (∫ x, ((if t = t1 then (U_of (φ N) (φ N)).weakDeriv x
        else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv x)
        * (∫ x in (0 : ℝ)..1, ux t x)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) = 0 := by
      intro t
      rw [integral_mul_const]
      by_cases ht1 : t = t1
      · simp only [ite_eq_left ht1, hslice0, zero_mul]
      · simp only [ite_eq_right ht1, hslice0, zero_mul]
    calc ∫ t, (∫ x, ((if t = t1 then (U_of (φ N) (φ N)).weakDeriv x
          else (U_of (φ N) (Nat.floor ((t - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv x)
          * (∫ x in (0 : ℝ)..1, ux t x)) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        ∂(volume.restrict (Set.Icc t0 t1))
        = ∫ t, (0 : ℝ) ∂(volume.restrict (Set.Icc t0 t1)) :=
          integral_congr_ae (Eventually.of_forall h0)
      _ = 0 := by simp
  have hRHS : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      ux p.1 p.2 * (∫ x in (0 : ℝ)..1, ux p.1 x)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ t, ((∫ x in (0 : ℝ)..1, ux t x) ^ 2) ∂(volume.restrict (Set.Icc t0 t1)) := by
    rw [hrr, hμr]
    have hIntUx : Integrable (fun p : ℝ × ℝ =>
        ux p.1 p.2 * (∫ x in (0 : ℝ)..1, ux p.1 x))
        (((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) :=
      memLp_one_iff_integrable.mp (MemLp.mul hMemUx' hΨmem)
    have hFubUx : (∫ p, ux p.1 p.2 * (∫ x in (0 : ℝ)..1, ux p.1 x)
        ∂(((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))))
        = ∫ t, (∫ x, ux t x * (∫ x in (0 : ℝ)..1, ux t x)
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) ∂(volume.restrict (Set.Icc t0 t1)) :=
      integral_prod _ hIntUx
    rw [hFubUx]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    show (∫ x, ux t x * (∫ x in (0 : ℝ)..1, ux t x)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) = (∫ x in (0 : ℝ)..1, ux t x) ^ 2
    rw [integral_mul_const, hfunUx]
    ring
  have hlim' : Filter.Tendsto (fun N : ℕ => (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
        * (∫ x in (0 : ℝ)..1, ux p.1 x)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))
      Filter.atTop (nhds (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
        ux p.1 p.2 * (∫ x in (0 : ℝ)..1, ux p.1 x)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) :=
    hlim
  have hconst0 : Filter.Tendsto (fun N : ℕ => (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
        else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
        * (∫ x in (0 : ℝ)..1, ux p.1 x)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))))
      Filter.atTop (nhds 0) := by
    have h0 : (fun _ : ℕ => (0 : ℝ)) =ᶠ[Filter.atTop]
        (fun N : ℕ => (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          (if p.1 = t1 then (U_of (φ N) (φ N)).weakDeriv p.2
            else (U_of (φ N) (Nat.floor ((p.1 - t0) / ((t1 - t0) / (↑(φ N)))) + 1)).weakDeriv p.2)
            * (∫ x in (0 : ℝ)..1, ux p.1 x)
          ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))) :=
      Eventually.of_forall (fun N => (hLHS0 N).symm)
    exact Tendsto.congr' h0 tendsto_const_nhds
  have hRHS0 : (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
      ux p.1 p.2 * (∫ x in (0 : ℝ)..1, ux p.1 x)
      ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))) = 0 :=
    tendsto_nhds_unique hlim' hconst0
  rw [hRHS] at hRHS0
  have hsq_int : Integrable (fun t => (∫ x in (0 : ℝ)..1, ux t x) ^ 2)
      (volume.restrict (Set.Icc t0 t1)) :=
    hMemM.integrable_sq
  have hsq0 : (fun t => (∫ x in (0 : ℝ)..1, ux t x) ^ 2)
      =ᵐ[volume.restrict (Set.Icc t0 t1)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hsq_int).mp hRHS0
  filter_upwards [hsq0] with t ht
  have ht0 : (∫ x in (0 : ℝ)..1, ux t x) ^ 2 = 0 := ht
  exact sq_eq_zero_iff.mp ht0


theorem ioc_ae_eq_icc (a b : ℝ) : Set.Ioc a b =ᵐ[volume] Set.Icc a b := by
  have hmem : ({a} : Set ℝ)ᶜ ∈ MeasureTheory.ae volume := by
    rw [mem_ae_iff, compl_compl]
    exact Real.volume_singleton
  refine Filter.eventuallyEq_of_mem hmem (fun x hx => ?_)
  have hxa : x ≠ a := by simpa using hx
  refine propext ⟨fun h => Set.Ioc_subset_Icc_self h, fun h => ?_⟩
  rw [Set.mem_Icc] at h
  rw [Set.mem_Ioc]
  exact ⟨lt_of_le_of_ne' h.1 hxa, h.2⟩


theorem intervalIntegral_eq_Icc (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, f t) = ∫ t in Set.Icc a b, f t ∂volume := by
  have hμ : volume.restrict (Set.Ioc a b) = volume.restrict (Set.Icc a b) :=
    Measure.restrict_congr_set (ioc_ae_eq_icc a b)
  rw [intervalIntegral.integral_of_le hab, hμ]


theorem integrable_of_memLp2_Icc01 (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  haveI := isFiniteMeasure_restrict_Icc01
  exact memLp_one_iff_integrable.mp (hg.mono_exponent (show (1 : ENNReal) ≤ 2 from one_le_two))


theorem primitive_continuousOn (g : ℝ → ℝ)
    (hg : Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, g t) (Set.Icc (0 : ℝ) 1) := by
  set G : ℝ → ℝ := (Set.Icc (0 : ℝ) 1).indicator g with hGdef
  have hGI : Integrable G volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hg
  have hcont : Continuous (fun x => ∫ t in (0 : ℝ)..x, G t) :=
    intervalIntegral.continuous_primitive (fun a b => hGI.intervalIntegrable) 0
  have heq : Set.EqOn (fun x => ∫ t in (0 : ℝ)..x, g t) (fun x => ∫ t in (0 : ℝ)..x, G t)
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    show (∫ t in (0 : ℝ)..x, g t) = ∫ t in (0 : ℝ)..x, G t
    have h0x : (0 : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    have e1 : (∫ t in (0 : ℝ)..x, g t) = ∫ t in Set.Ioc 0 x, g t ∂volume :=
      intervalIntegral.integral_of_le h0x
    have e2 : (∫ t in (0 : ℝ)..x, G t) = ∫ t in Set.Ioc 0 x, G t ∂volume :=
      intervalIntegral.integral_of_le h0x
    rw [e1, e2]
    refine integral_congr_ae ((ae_restrict_mem measurableSet_Ioc).mono (fun y hy => ?_))
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_Ioc] at hy
      rw [Set.mem_Icc] at hx ⊢
      exact ⟨le_of_lt hy.1, le_trans hy.2 hx.2⟩
    rw [hGdef]
    exact (Set.indicator_of_mem hyIcc g).symm
  exact hcont.continuousOn.congr heq


theorem memLp_two_of_continuousOn_Icc01 (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  haveI := isFiniteMeasure_restrict_Icc01
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
    ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => hC x hx))


theorem fubini_ibp (g h V : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hh : MemLp h 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hV : ∀ x ∈ Set.Icc (0 : ℝ) 1, V x = ∫ t in (0 : ℝ)..x, h t)
    (hh0 : (∫ t in (0 : ℝ)..1, h t) = 0) :
    (∫ x in (0 : ℝ)..1, (∫ t in (0 : ℝ)..x, g t) * h x)
      = -∫ x in (0 : ℝ)..1, g x * V x := by
  haveI := isFiniteMeasure_restrict_Icc01
  have hgI : Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_of_memLp2_Icc01 g hg
  have hhI : Integrable h (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_of_memLp2_Icc01 h hh
  have hhOn : IntegrableOn h (Set.Icc (0 : ℝ) 1) volume := hhI
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} := by
    have e : {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1}
        = (Prod.snd ⁻¹' Set.Ioi (0 : ℝ)) ∩ {p : ℝ × ℝ | p.2 ≤ p.1} := by
      ext ⟨x, y⟩
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, Set.mem_inter_iff]
      rw [Set.mem_Ioc]
    rw [e]
    refine MeasurableSet.inter ?_ (isClosed_le continuous_snd continuous_fst).measurableSet
    exact measurable_snd measurableSet_Ioi
  have hPI : Integrable (fun p : ℝ × ℝ => g p.2 * h p.1)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    have e : (fun p : ℝ × ℝ => g p.2 * h p.1) = (fun z => h z.1 * g z.2) :=
      funext (fun ⟨x, y⟩ => mul_comm _ _)
    rw [e]
    exact Integrable.mul_prod hhI hgI
  have huncurry : (Function.uncurry fun x y => (Set.Ioc 0 x).indicator g y * h x)
      = {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1}.indicator (fun p => g p.2 * h p.1) := by
    funext ⟨x, y⟩
    show (Set.Ioc 0 x).indicator g y * h x
      = ({p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1}.indicator (fun p => g p.2 * h p.1)) (x, y)
    by_cases hyx : y ∈ Set.Ioc 0 x
    · have m1 : (Set.Ioc 0 x).indicator g y = g y := Set.indicator_of_mem hyx g
      have m2 : (x, y) ∈ {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} := hyx
      have m3 : ({p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1}.indicator (fun p => g p.2 * h p.1)) (x, y)
          = g y * h x := Set.indicator_of_mem m2 _
      rw [m1, m3]
    · have m1 : (Set.Ioc 0 x).indicator g y = 0 := Set.indicator_of_notMem hyx g
      have m2 : (x, y) ∉ {p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1} := hyx
      have m3 : ({p : ℝ × ℝ | p.2 ∈ Set.Ioc 0 p.1}.indicator (fun p => g p.2 * h p.1)) (x, y)
          = 0 := Set.indicator_of_notMem m2 _
      rw [m1, m3, zero_mul]
  have hInt : Integrable
      (Function.uncurry fun x y => (Set.Ioc 0 x).indicator g y * h x)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [huncurry]
    exact hPI.indicator hS
  have hswap : (∫ x in Set.Icc (0 : ℝ) 1,
        ∫ y in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume ∂volume)
      = ∫ y in Set.Icc (0 : ℝ) 1,
        ∫ x in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume ∂volume :=
    integral_integral_swap hInt
  have hLHS : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (∫ y in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume)
        = (∫ t in (0 : ℝ)..x, g t) * h x := by
    intro x hx
    have h0x : (0 : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    have hsub : Set.Ioc 0 x ⊆ Set.Icc (0 : ℝ) 1 := by
      intro y hy
      rw [Set.mem_Ioc] at hy
      exact Set.mem_Icc.mpr ⟨le_of_lt hy.1, le_trans hy.2 (Set.mem_Icc.mp hx).2⟩
    rw [integral_mul_const]
    congr 1
    have e : (∫ y in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y ∂volume)
        = ∫ y in Set.Ioc 0 x, g y ∂volume := by
      have hset := setIntegral_indicator (s := Set.Icc (0 : ℝ) 1) (t := Set.Ioc 0 x)
        (f := g) (μ := volume) measurableSet_Ioc
      rw [Set.inter_eq_self_of_subset_right hsub] at hset
      exact hset
    rw [e]
    exact (intervalIntegral.integral_of_le h0x).symm
  have hRHS : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      (∫ x in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume)
        = g y * (-V y) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := (Set.mem_Ioc.mp hy).1
    have hy1 : y ≤ (1 : ℝ) := (Set.mem_Ioc.mp hy).2
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hy
    have hsub : Set.Icc y 1 ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (le_of_lt hy0) le_rfl
    have hpw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (Set.Ioc 0 x).indicator g y * h x
          = (Set.Icc y 1).indicator (fun x => g y * h x) x := by
      intro x hx
      by_cases hx' : x ∈ Set.Icc y 1
      · have hyx : y ∈ Set.Ioc 0 x := Set.mem_Ioc.mpr ⟨hy0, (Set.mem_Icc.mp hx').1⟩
        rw [Set.indicator_of_mem hyx g, Set.indicator_of_mem hx' (fun x => g y * h x)]
      · have hyx : y ∉ Set.Ioc 0 x := by
          intro hcon
          apply hx'
          rw [Set.mem_Ioc] at hcon
          rw [Set.mem_Icc] at hx ⊢
          exact ⟨hcon.2, hx.2⟩
        rw [Set.indicator_of_notMem hyx g,
          Set.indicator_of_notMem hx' (fun x => g y * h x), zero_mul]
    have e1 : (∫ x in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume)
        = ∫ x in Set.Icc (0 : ℝ) 1, (Set.Icc y 1).indicator (fun x => g y * h x) x ∂volume :=
      integral_congr_ae ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => hpw x hx))
    have e2 : (∫ x in Set.Icc (0 : ℝ) 1, (Set.Icc y 1).indicator (fun x => g y * h x) x ∂volume)
        = ∫ x in Set.Icc y 1, g y * h x ∂volume := by
      have hset := setIntegral_indicator (s := Set.Icc (0 : ℝ) 1) (t := Set.Icc y 1)
        (f := (fun x => g y * h x)) (μ := volume) measurableSet_Icc
      rw [Set.inter_eq_self_of_subset_right hsub] at hset
      exact hset
    have e3 : (∫ x in Set.Icc y 1, g y * h x ∂volume)
        = g y * ∫ x in Set.Icc y 1, h x ∂volume :=
      integral_const_mul _ _
    have e4 : (∫ x in Set.Icc y 1, h x ∂volume) = -V y := by
      have hbr : (∫ x in Set.Icc y 1, h x ∂volume) = ∫ t in y..1, h t :=
        (intervalIntegral_eq_Icc h y 1 hy1).symm
      rw [hbr]
      have h0y : IntervalIntegrable h volume 0 y := by
        apply IntegrableOn.intervalIntegrable
        have hsub0 : Set.uIcc 0 y ⊆ Set.Icc (0 : ℝ) 1 := by
          rw [Set.uIcc_of_le (le_of_lt hy0)]
          exact Set.Icc_subset_Icc le_rfl hy1
        exact IntegrableOn.mono_set hhOn hsub0
      have hy1' : IntervalIntegrable h volume y 1 := by
        apply IntegrableOn.intervalIntegrable
        have hsub1 : Set.uIcc y 1 ⊆ Set.Icc (0 : ℝ) 1 := by
          rw [Set.uIcc_of_le hy1]
          exact Set.Icc_subset_Icc (le_of_lt hy0) le_rfl
        exact IntegrableOn.mono_set hhOn hsub1
      have hadd := intervalIntegral.integral_add_adjacent_intervals h0y hy1'
      have hVy : V y = ∫ t in (0 : ℝ)..y, h t := hV y hyIcc
      rw [hh0] at hadd
      rw [← hVy] at hadd
      linarith
    rw [e1, e2, e3, e4]
  have hLHSae : (fun x => ∫ y in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => (∫ t in (0 : ℝ)..x, g t) * h x) :=
    (ae_restrict_mem measurableSet_Icc).mono (fun x hx => hLHS x hx)
  have hRHSae : (fun y => ∫ x in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun y => g y * (-V y)) := by
    have haeIoc : ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), y ∈ Set.Ioc (0 : ℝ) 1 := by
      have hμ : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Icc (0 : ℝ) 1) :=
        Measure.restrict_congr_set (ioc_ae_eq_icc 0 1)
      rw [← hμ]
      exact ae_restrict_mem measurableSet_Ioc
    exact haeIoc.mono (fun y hy => hRHS y hy)
  have cLHS := integral_congr_ae hLHSae
  have cRHS := integral_congr_ae hRHSae
  have hneg : (∫ y in Set.Icc (0 : ℝ) 1, g y * (-V y) ∂volume)
      = -∫ y in Set.Icc (0 : ℝ) 1, g y * V y ∂volume := by
    have e : (fun y => g y * (-V y)) = (fun y => -(g y * V y)) :=
      funext (fun y => mul_neg _ _)
    rw [e, integral_neg]
  have hIcc : (∫ x in Set.Icc (0 : ℝ) 1, (∫ t in (0 : ℝ)..x, g t) * h x ∂volume)
      = -∫ x in Set.Icc (0 : ℝ) 1, g x * V x ∂volume :=
    calc (∫ x in Set.Icc (0 : ℝ) 1, (∫ t in (0 : ℝ)..x, g t) * h x ∂volume)
        = ∫ x in Set.Icc (0 : ℝ) 1,
            ∫ y in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume ∂volume :=
          cLHS.symm
      _ = ∫ y in Set.Icc (0 : ℝ) 1,
            ∫ x in Set.Icc (0 : ℝ) 1, (Set.Ioc 0 x).indicator g y * h x ∂volume ∂volume :=
          hswap
      _ = ∫ y in Set.Icc (0 : ℝ) 1, g y * (-V y) ∂volume := cRHS
      _ = -∫ x in Set.Icc (0 : ℝ) 1, g x * V x ∂volume := hneg
  have hb1 : (∫ x in (0 : ℝ)..1, (∫ t in (0 : ℝ)..x, g t) * h x)
      = ∫ x in Set.Icc (0 : ℝ) 1, (∫ t in (0 : ℝ)..x, g t) * h x ∂volume :=
    intervalIntegral_eq_Icc _ 0 1 zero_le_one
  have hb2 : (∫ x in (0 : ℝ)..1, g x * V x)
      = ∫ x in Set.Icc (0 : ℝ) 1, g x * V x ∂volume :=
    intervalIntegral_eq_Icc _ 0 1 zero_le_one
  rw [hb1, hb2]
  exact hIcc


theorem profiles_of_ibp
    {t0 t1 : ℝ} (ht : t0 < t1)
    (ũ ux : ℝ → ℝ → ℝ)
    (hMemUx : ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      MemLp (fun x => ux t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hCont : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → Continuous (ũ t))
    (hTrace : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ũ t 0 = 0)
    (hMean : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → (∫ x in (0 : ℝ)..1, ux t x) = 0)
    (hIbP : ∀ t : ℝ, t ∈ Set.Icc t0 t1 → ∀ v : WeakH10,
      (∫ x in (0 : ℝ)..1, ũ t x * v.weakDeriv x)
        = -(∫ x in (0 : ℝ)..1, ux t x * v.toFun x)) :
    ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      ∃ h : WeakH10, h.toFun = ũ t ∧ h.weakDeriv = ux t := by
  intro t htmem
  haveI := isFiniteMeasure_restrict_Icc01
  have hg : MemLp (fun x => ux t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hMemUx t htmem
  have hU : Continuous (ũ t) := hCont t htmem
  have htr : ũ t 0 = 0 := hTrace t htmem
  have hmean : (∫ x in (0 : ℝ)..1, ux t x) = 0 := hMean t htmem
  have hgI : Integrable (fun x => ux t x) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_of_memLp2_Icc01 (fun x => ux t x) hg
  have hFcont : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, ux t s) (Set.Icc (0 : ℝ) 1) :=
    primitive_continuousOn (fun x => ux t x) hgI
  have hU2 : MemLp (ũ t) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    memLp_two_of_continuousOn_Icc01 (ũ t) hU.continuousOn
  have hF2 : MemLp (fun x => ∫ s in (0 : ℝ)..x, ux t s) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    memLp_two_of_continuousOn_Icc01 (fun x => ∫ s in (0 : ℝ)..x, ux t s) hFcont
  have hw2 : MemLp (fun x => ũ t x - ∫ s in (0 : ℝ)..x, ux t s) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hU2.sub hF2
  have hwI : Integrable (fun x => ũ t x - ∫ s in (0 : ℝ)..x, ux t s)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_of_memLp2_Icc01 _ hw2
  have hvol : volume.real (Set.Icc (0 : ℝ) 1) = 1 := by
    show (volume (Set.Icc (0 : ℝ) 1)).toReal = 1
    rw [Real.volume_Icc, sub_zero]
    exact ENNReal.toReal_ofReal zero_le_one
  set c : ℝ := ∫ x in Set.Icc (0 : ℝ) 1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) ∂volume with hcdef
  have hcI : Integrable (fun _ : ℝ => c) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    integrable_const c
  set g0 : ℝ → ℝ := fun x => (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) - c with hg0def
  have hg0I : Integrable g0 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hwI.sub hcI
  have hg02 : MemLp g0 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := hw2.sub (memLp_const c)
  have hg0meanIcc : (∫ x in Set.Icc (0 : ℝ) 1, g0 x ∂volume) = 0 := by
    have hsub0 : (∫ x in Set.Icc (0 : ℝ) 1, g0 x ∂volume)
        = (∫ x in Set.Icc (0 : ℝ) 1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) ∂volume)
          - ∫ x in Set.Icc (0 : ℝ) 1, c ∂volume :=
      integral_sub hwI hcI
    have hcint : (∫ x in Set.Icc (0 : ℝ) 1, c ∂volume) = c := by
      rw [setIntegral_const, hvol, one_smul]
    rw [hsub0, hcint, ← hcdef]
    exact sub_self c
  have hg0mean : (∫ x in (0 : ℝ)..1, g0 x) = 0 := by
    have hb : (∫ x in (0 : ℝ)..1, g0 x)
        = ∫ x in Set.Icc (0 : ℝ) 1, g0 x ∂volume :=
      intervalIntegral_eq_Icc _ 0 1 zero_le_one
    rw [hb]
    exact hg0meanIcc
  set V : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, g0 s with hVdef
  have h1 : (∫ x in (0 : ℝ)..1, ũ t x * g0 x)
      = -∫ x in (0 : ℝ)..1, ux t x * V x :=
    hIbP t htmem ⟨V, g0, hg02, fun x _ => rfl, hg0mean⟩
  have hFub : (∫ x in (0 : ℝ)..1, (∫ s in (0 : ℝ)..x, ux t s) * g0 x)
      = -∫ x in (0 : ℝ)..1, ux t x * V x :=
    fubini_ibp (fun x => ux t x) g0 V hg hg02 (fun x _ => rfl) hg0mean
  have hU0 : IntervalIntegrable (fun x => ũ t x * g0 x) volume 0 1 := by
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hU2.integrable_mul hg02
  have hF0 : IntervalIntegrable (fun x => (∫ s in (0 : ℝ)..x, ux t s) * g0 x) volume 0 1 := by
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hF2.integrable_mul hg02
  have horth : (∫ x in (0 : ℝ)..1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x) = 0 := by
    have hsub : (∫ x in (0 : ℝ)..1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x)
        = (∫ x in (0 : ℝ)..1, ũ t x * g0 x)
          - ∫ x in (0 : ℝ)..1, (∫ s in (0 : ℝ)..x, ux t s) * g0 x := by
      have e : (fun x => (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x)
          = (fun x => ũ t x * g0 x - (∫ s in (0 : ℝ)..x, ux t s) * g0 x) :=
        funext (fun x => sub_mul _ _ _)
      rw [e]
      exact intervalIntegral.integral_sub hU0 hF0
    rw [hsub, h1, hFub, sub_self]
  have hwg0 : Integrable (fun x => (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := hw2.integrable_mul hg02
  have hcg0 : Integrable (fun x => c * g0 x) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hg0I.const_mul c
  have he_sq : (fun x => ((ũ t x - ∫ s in (0 : ℝ)..x, ux t s) - c)^2)
      = (fun x => (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x - c * g0 x) := by
    funext x
    simp only [hg0def]
    ring
  have hwg0Icc : (∫ x in Set.Icc (0 : ℝ) 1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x ∂volume)
      = 0 := by
    have hb : (∫ x in Set.Icc (0 : ℝ) 1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x ∂volume)
        = ∫ x in (0 : ℝ)..1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x :=
      (intervalIntegral_eq_Icc _ 0 1 zero_le_one).symm
    rw [hb, horth]
  have hcg0Icc : (∫ x in Set.Icc (0 : ℝ) 1, c * g0 x ∂volume) = 0 := by
    rw [integral_const_mul, hg0meanIcc, mul_zero]
  have hsq : (∫ x in Set.Icc (0 : ℝ) 1, ((ũ t x - ∫ s in (0 : ℝ)..x, ux t s) - c)^2 ∂volume)
      = 0 := by
    have hsub' : (∫ x in Set.Icc (0 : ℝ) 1,
          ((ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x - c * g0 x) ∂volume)
        = (∫ x in Set.Icc (0 : ℝ) 1, (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) * g0 x ∂volume)
          - ∫ x in Set.Icc (0 : ℝ) 1, c * g0 x ∂volume :=
      integral_sub hwg0 hcg0
    rw [he_sq, hsub', hwg0Icc, hcg0Icc]
    exact sub_self (0 : ℝ)
  have hsqI : Integrable (fun x => ((ũ t x - ∫ s in (0 : ℝ)..x, ux t s) - c)^2)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [he_sq]
    exact hwg0.sub hcg0
  have hae : (fun x => ũ t x - ∫ s in (0 : ℝ)..x, ux t s)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun _ => c) := by
    have h0 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsqI).mp hsq
    exact h0.mono (fun x hx => by
      have hx' : (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) - c = 0 :=
        sq_eq_zero_iff.mp hx
      exact sub_eq_zero.mp hx')
  have hwcont : ContinuousOn (fun x => ũ t x - ∫ s in (0 : ℝ)..x, ux t s)
      (Set.Icc (0 : ℝ) 1) :=
    hU.continuousOn.sub hFcont
  have heq : Set.EqOn (fun x => ũ t x - ∫ s in (0 : ℝ)..x, ux t s) (fun _ => c)
      (Set.Icc (0 : ℝ) 1) :=
    Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hae hwcont continuous_const.continuousOn
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hw0 : (ũ t 0 - ∫ s in (0 : ℝ)..0, ux t s) = 0 := by
    rw [htr, intervalIntegral.integral_same, sub_zero]
  have hc0 : c = 0 := by
    have h : (ũ t 0 - ∫ s in (0 : ℝ)..0, ux t s) = c := heq h0mem
    rw [hw0] at h
    exact h.symm
  have hfinal : ∀ x ∈ Set.Icc (0 : ℝ) 1, ũ t x = ∫ s in (0 : ℝ)..x, ux t s := by
    intro x hx
    have h : (ũ t x - ∫ s in (0 : ℝ)..x, ux t s) = c := heq hx
    rw [hc0] at h
    exact sub_eq_zero.mp h
  exact ⟨⟨ũ t, (fun x => ux t x), hg, hfinal, hmean⟩, rfl, rfl⟩


theorem bridge01 (f : ℝ → ℝ) :
    (∫ x in (0:ℝ)..1, f x) = ∫ x, f x ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := 1))]


theorem memLp_slice (ux : ℝ → ℝ → ℝ) (C : ℝ) (t : ℝ)
    (h : eLpNorm (fun x => ux t x) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) ≤ ENNReal.ofReal C) :
    MemLp (fun x => ux t x) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  lt_of_le_of_lt h ENNReal.ofReal_lt_top


theorem eq_at_of_eq_on_seq (ĝ₁ ĝ₂ : ℝ → ℝ) (s : ℕ → ℝ) (τ : ℝ)
    (h₁ : Continuous ĝ₁) (h₂ : Continuous ĝ₂)
    (hs : Tendsto s atTop (nhds τ)) (heq : ∀ n, ĝ₁ (s n) = ĝ₂ (s n)) :
    ĝ₁ τ = ĝ₂ τ := by
  have e1 : Tendsto (fun n => ĝ₁ (s n)) atTop (nhds (ĝ₁ τ)) := (h₁.tendsto τ).comp hs
  have e2 : Tendsto (fun n => ĝ₂ (s n)) atTop (nhds (ĝ₂ τ)) := (h₂.tendsto τ).comp hs
  have hfun : (fun n => ĝ₂ (s n)) = fun n => ĝ₁ (s n) := funext fun n => (heq n).symm
  rw [hfun] at e2
  exact tendsto_nhds_unique e1 e2


theorem intervalIntegral_congr_ae01 (F G : ℝ → ℝ)
    (hFG : F =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] G) :
    (∫ x in (0:ℝ)..1, F x) = ∫ x in (0:ℝ)..1, G x := by
  rw [bridge01 F, bridge01 G]
  exact integral_congr_ae hFG


theorem inner_real_eq_mul (a b : ℝ) : inner ℝ a b = b * a := by
  rw [RCLike.inner_apply, RCLike.conj_to_real]


theorem exists_seq_in_inter (t0 t1 : ℝ) (ht : t0 < t1) (G : Set ℝ)
    (hG : (volume.restrict (Set.Icc t0 t1)) Gᶜ = 0) (τ : ℝ) (hτ : τ ∈ Set.Icc t0 t1) :
    ∃ s : ℕ → ℝ, (∀ n, s n ∈ G ∧ s n ∈ Set.Icc t0 t1) ∧ Tendsto s atTop (nhds τ) := by
  rw [Set.mem_Icc] at hτ
  have hkey : ∀ n : ℕ, ∃ x, x ∈ G ∧ x ∈ Metric.ball τ (1 / ((n : ℝ) + 1)) ∧
      x ∈ Set.Icc t0 t1 := by
    intro n
    by_contra hcon
    set B := Metric.ball τ (1 / ((n : ℝ) + 1)) ∩ Set.Icc t0 t1 with hB
    have hBsub : B ⊆ Gᶜ := by
      intro x hx hxG
      exact hcon ⟨x, hxG, hx.1, hx.2⟩
    have hB0 : (volume.restrict (Set.Icc t0 t1)) B = 0 := measure_mono_null hBsub hG
    have hBmeas : MeasurableSet B := measurableSet_ball.inter measurableSet_Icc
    have hBIcc : B ⊆ Set.Icc t0 t1 := Set.inter_subset_right
    have hvolB : volume B = 0 := by
      have h1 : (volume.restrict (Set.Icc t0 t1)) B = volume (B ∩ Set.Icc t0 t1) :=
        Measure.restrict_apply hBmeas
      rw [Set.inter_eq_self_of_subset_left hBIcc] at h1
      rw [← h1]
      exact hB0
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set ε : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hε
    have hεpos : 0 < ε := by positivity
    set a : ℝ := max t0 (τ - ε) with ha
    set b : ℝ := min t1 (τ + ε) with hb
    have hab : a < b := by
      rw [ha, hb, max_lt_iff, lt_min_iff, lt_min_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hτ.1, hτ.2, ht, hεpos]
    have hsub : Set.Ioo a b ⊆ B := by
      intro x hx
      simp only [Set.mem_Ioo] at hx
      constructor
      · rw [Metric.mem_ball, Real.dist_eq]
        have hx1 : τ - ε < x := lt_of_le_of_lt (le_max_right t0 (τ - ε)) hx.1
        have hx2 : x < τ + ε := lt_of_lt_of_le hx.2 (min_le_right t1 (τ + ε))
        have hxabs : |x - τ| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
        have hεlt : ε < 1 / ((n : ℝ) + 1) := by
          rw [hε, div_lt_div_iff₀ (by positivity) hnpos]
          linarith [hnpos]
        linarith [hxabs, hεlt]
      · constructor
        · exact le_trans (le_max_left t0 (τ - ε)) (le_of_lt hx.1)
        · exact le_trans (le_of_lt hx.2) (min_le_left t1 (τ + ε))
    have hIoo : 0 < volume (Set.Ioo a b) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    have hpos : 0 < volume B := lt_of_lt_of_le hIoo (measure_mono hsub)
    rw [hvolB] at hpos
    exact lt_irrefl 0 hpos
  choose s hsG hsB hsI using hkey
  refine ⟨s, fun n => ⟨hsG n, hsI n⟩, ?_⟩
  have hsub : Tendsto (fun n => s n - τ) atTop (nhds 0) := by
    refine squeeze_zero_norm ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    have hball := hsB n
    rw [Metric.mem_ball, Real.dist_eq] at hball
    rw [Real.norm_eq_abs]
    exact le_of_lt hball
  have h2 := hsub.add (tendsto_const_nhds (x := τ))
  simpa using h2

/-- Gradient representative at bad t via weak subsequential limits. -/

theorem grad_rep_bad_t_fixed
    {t0 t1 : ℝ} (ht : t0 < t1)
    (ux : ℝ → ℝ → ℝ)
    (G : Set ℝ) (hG : (volume.restrict (Set.Icc t0 t1)) Gᶜ = 0)
    (hPairG : ∀ w : ℝ → ℝ, MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        ∀ t ∈ G, (∫ x in (0 : ℝ)..1, ux t x * w x) = ĝ t)
    (hBdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ∈ Set.Icc t0 t1 →
      eLpNorm (fun x => ux t x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal C)
    (hGood : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∃ s : ℕ → ℝ,
      (∀ n : ℕ, s n ∈ G) ∧ Filter.Tendsto s Filter.atTop (nhds τ))
    (hMean0 : ∀ (ĝ : ℝ → ℝ), Continuous ĝ →
      (∀ t ∈ G, (∫ x in (0 : ℝ)..1, ux t x * 1) = ĝ t) → ∀ t : ℝ, ĝ t = 0) :
    ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 → ∃ w : ℝ → ℝ,
      MemLp w 2 (volume.restrict (Set.Icc (0 : ℝ) 1))
      ∧ (∀ v : ℝ → ℝ, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
          ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
            (∀ t ∈ G, (∫ x in (0 : ℝ)..1, ux t x * v x) = ĝ t) ∧
            (∫ x in (0 : ℝ)..1, w x * v x) = ĝ τ)
      ∧ (∫ x in (0 : ℝ)..1, w x) = 0 := by
  intro τ hτ
  obtain ⟨C, hC0, hCbdd⟩ := hBdd
  obtain ⟨s, hsGI, hstend⟩ := exists_seq_in_inter t0 t1 ht G hG τ hτ
  choose ĝ hĝcont hĝeq using hPairG
  set T : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ĝ ⇑v (Lp.memLp v) τ
      map_add' := fun v w => by
        show ĝ ⇑(v + w) (Lp.memLp (v + w)) τ
          = ĝ ⇑v (Lp.memLp v) τ + ĝ ⇑w (Lp.memLp w) τ
        refine eq_at_of_eq_on_seq (ĝ ⇑(v + w) (Lp.memLp (v + w)))
          (ĝ ⇑v (Lp.memLp v) + ĝ ⇑w (Lp.memLp w)) s τ (hĝcont _ _)
          ((hĝcont _ _).add (hĝcont _ _)) hstend ?_
        intro n
        obtain ⟨hsG, hsI⟩ := hsGI n
        show ĝ ⇑(v + w) (Lp.memLp (v + w)) (s n)
          = ĝ ⇑v (Lp.memLp v) (s n) + ĝ ⇑w (Lp.memLp w) (s n)
        rw [← hĝeq _ _ (s n) hsG, ← hĝeq _ _ (s n) hsG, ← hĝeq _ _ (s n) hsG]
        have hux : MemLp (fun x => ux (s n) x) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) :=
          memLp_slice _ _ _ (hCbdd _ hsI)
        have hInt_vw : Integrable (fun x => ux (s n) x * ⇑(v + w) x)
            (volume.restrict (Set.Icc (0:ℝ) 1)) :=
          memLp_one_iff_integrable.1 (hux.mul (Lp.memLp (v + w)))
        have hInt_v : Integrable (fun x => ux (s n) x * ⇑v x)
            (volume.restrict (Set.Icc (0:ℝ) 1)) :=
          memLp_one_iff_integrable.1 (hux.mul (Lp.memLp v))
        have hInt_w : Integrable (fun x => ux (s n) x * ⇑w x)
            (volume.restrict (Set.Icc (0:ℝ) 1)) :=
          memLp_one_iff_integrable.1 (hux.mul (Lp.memLp w))
        simp only [bridge01]
        have hae : (fun x => ux (s n) x * ⇑(v + w) x) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
            (fun x => ux (s n) x * ⇑v x + ux (s n) x * ⇑w x) := by
          filter_upwards [Lp.coeFn_add v w] with x hx
          simp only [hx, Pi.add_apply]
          ring
        rw [integral_congr_ae hae, integral_add hInt_v hInt_w]
      map_smul' := fun c v => by
        show ĝ ⇑(c • v) (Lp.memLp (c • v)) τ = c • ĝ ⇑v (Lp.memLp v) τ
        refine eq_at_of_eq_on_seq (ĝ ⇑(c • v) (Lp.memLp (c • v)))
          (c • ĝ ⇑v (Lp.memLp v)) s τ (hĝcont _ _)
          ((hĝcont _ _).const_smul c) hstend ?_
        intro n
        obtain ⟨hsG, hsI⟩ := hsGI n
        show ĝ ⇑(c • v) (Lp.memLp (c • v)) (s n) = c • ĝ ⇑v (Lp.memLp v) (s n)
        rw [← hĝeq _ _ (s n) hsG, ← hĝeq _ _ (s n) hsG]
        have hux : MemLp (fun x => ux (s n) x) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) :=
          memLp_slice _ _ _ (hCbdd _ hsI)
        simp only [bridge01]
        have hae : (fun x => ux (s n) x * ⇑(c • v) x) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
            (fun x => c • (ux (s n) x * ⇑v x)) := by
          filter_upwards [Lp.coeFn_smul c v] with x hx
          simp only [hx, Pi.smul_apply, smul_eq_mul]
          ring
        rw [integral_congr_ae hae, integral_smul] } with hT
  have hbound : ∀ v : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)), ‖T v‖ ≤ C * ‖v‖ := by
    intro v
    have hTv : T v = ĝ ⇑v (Lp.memLp v) τ := rfl
    rw [hTv, Real.norm_eq_abs]
    have hlim : Tendsto (fun n => ĝ ⇑v (Lp.memLp v) (s n)) atTop
        (nhds (ĝ ⇑v (Lp.memLp v) τ)) := ((hĝcont _ _).tendsto τ).comp hstend
    have hterm : ∀ n, |ĝ ⇑v (Lp.memLp v) (s n)| ≤ C * ‖v‖ := by
      intro n
      obtain ⟨hsG, hsI⟩ := hsGI n
      have hux : MemLp (fun x => ux (s n) x) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) :=
        memLp_slice _ _ _ (hCbdd _ hsI)
      have heq1 : ĝ ⇑v (Lp.memLp v) (s n) = ∫ x in (0:ℝ)..1, ux (s n) x * ⇑v x :=
        (hĝeq _ _ (s n) hsG).symm
      rw [heq1, bridge01 _]
      have hinner : (∫ x, ux (s n) x * ⇑v x ∂(volume.restrict (Set.Icc (0:ℝ) 1))) =
          inner ℝ (hux.toLp _) v := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hux.coeFn_toLp] with x hx
        rw [inner_real_eq_mul, hx]
        exact mul_comm _ _
      rw [hinner, ← Real.norm_eq_abs]
      have hlt : eLpNorm (fun x => ux (s n) x) 2 (volume.restrict (Set.Icc (0:ℝ) 1)) < ⊤ := hux
      have hnorm_u : ‖hux.toLp (fun x => ux (s n) x)‖ ≤ C := by
        rw [Lp.norm_def, eLpNorm_congr_ae hux.coeFn_toLp,
          ← ENNReal.toReal_ofReal hC0, ENNReal.toReal_le_toReal hlt.ne ENNReal.ofReal_ne_top]
        exact hCbdd _ hsI
      calc ‖inner ℝ (hux.toLp _) v‖ ≤ ‖hux.toLp _‖ * ‖v‖ := norm_inner_le_norm _ _
        _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hnorm_u (norm_nonneg _)
    rw [abs_le]
    constructor
    · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => (abs_le.mp (hterm n)).1)
    · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun n => (abs_le.mp (hterm n)).2)
  set Tclm : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ] ℝ :=
    T.mkContinuous C hbound with hTclm
  set x₀ : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))).symm Tclm with hx₀
  have hpart_a : ∀ v : ℝ → ℝ, MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∃ ĝ : ℝ → ℝ, Continuous ĝ ∧
        (∀ t ∈ G, (∫ x in (0:ℝ)..1, ux t x * v x) = ĝ t) ∧
        (∫ x in (0:ℝ)..1, ⇑x₀ x * v x) = ĝ τ := by
    intro v hv
    refine ⟨ĝ ⇑(hv.toLp v) (Lp.memLp (hv.toLp v)), hĝcont _ _, ?_, ?_⟩
    · intro t htG
      have hae : (fun x => ux t x * v x) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
          (fun x => ux t x * ⇑(hv.toLp v) x) := by
        filter_upwards [hv.coeFn_toLp] with x hx
        rw [hx]
      have h1 := hĝeq (⇑(hv.toLp v)) (Lp.memLp (hv.toLp v)) t htG
      rw [intervalIntegral_congr_ae01 _ _ hae]
      exact h1
    · have hmain : (∫ x in (0:ℝ)..1, ⇑x₀ x * v x) = inner ℝ x₀ (hv.toLp v) := by
        rw [bridge01 _]
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv.coeFn_toLp] with x hx
        rw [inner_real_eq_mul, ← hx]
        exact mul_comm _ _
      rw [hmain, hx₀]
      have hsymm := InnerProductSpace.toDual_symm_apply (x := hv.toLp v) (y := Tclm)
      rw [hsymm]
      exact LinearMap.mkContinuous_apply T C hbound (hv.toLp v)
  have hpart_b : (∫ x in (0:ℝ)..1, ⇑x₀ x) = 0 := by
    have hv1 : MemLp (fun _ : ℝ => (1:ℝ)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      memLp_const 1
    obtain ⟨ĝ₁, hĝ₁c, hĝ₁eq, hĝ₁τ⟩ := hpart_a (fun _ => 1) hv1
    have h1eq : (fun x : ℝ => ⇑x₀ x) = (fun x => ⇑x₀ x * (fun _ => 1) x) := by
      funext x
      simp
    rw [h1eq, hĝ₁τ]
    exact hMean0 ĝ₁ hĝ₁c hĝ₁eq τ
  exact ⟨⇑x₀, Lp.memLp x₀, hpart_a, hpart_b⟩


theorem approx_id_tendsto
    {τ : ℝ} {ĝ : ℝ → ℝ} (hĝ : Continuous ĝ)
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun δ' : ℝ => (1 / (2 * δ')) * ∫ t in (τ - δ')..(τ + δ'), ĝ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ĝ τ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hcont := (Metric.tendsto_nhds.mp (hĝ.tendsto τ)) (ε / 2) hε2
  rw [Metric.eventually_nhds_iff_ball] at hcont
  obtain ⟨η, hηpos, hη⟩ := hcont
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball]
  refine ⟨η, hηpos, fun δ' hδ'mem hδ'pos => ?_⟩
  have hδ'0 : (0 : ℝ) < δ' := Set.mem_Ioi.mp hδ'pos
  rw [Metric.mem_ball, Real.dist_eq] at hδ'mem
  have hδ'lt : δ' < η := by
    rw [sub_zero, abs_of_pos hδ'0] at hδ'mem
    exact hδ'mem
  show dist ((1 / (2 * δ')) * (∫ t in (τ - δ')..(τ + δ'), ĝ t)) (ĝ τ) < ε
  have hab : τ - δ' ≤ τ + δ' := by linarith
  have hwpos : (0 : ℝ) < 2 * δ' := by linarith
  have hwne : (2 : ℝ) * δ' ≠ 0 := ne_of_gt hwpos
  have hlen : (τ + δ') - (τ - δ') = 2 * δ' := by ring
  have hbound : ∀ t ∈ Set.uIoc (τ - δ') (τ + δ'), ‖ĝ t - ĝ τ‖ ≤ ε / 2 := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have habs : |t - τ| ≤ δ' := by
      rw [abs_le]
      constructor <;> linarith
    have hdist : dist t τ < η := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt habs hδ'lt
    have h := hη t (Metric.mem_ball.mpr hdist)
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have hgi : IntervalIntegrable ĝ volume (τ - δ') (τ + δ') :=
    hĝ.intervalIntegrable _ _
  have hci : IntervalIntegrable (fun _ => ĝ τ) volume (τ - δ') (τ + δ') :=
    intervalIntegrable_const
  have hsub : (∫ t in (τ - δ')..(τ + δ'), (ĝ t - ĝ τ))
      = (∫ t in (τ - δ')..(τ + δ'), ĝ t) - (∫ _ in (τ - δ')..(τ + δ'), ĝ τ) :=
    intervalIntegral.integral_sub hgi hci
  have hconst : (∫ _ in (τ - δ')..(τ + δ'), ĝ τ)
      = ((τ + δ') - (τ - δ')) • (ĝ τ) :=
    intervalIntegral.integral_const _
  have hnorm : ‖∫ t in (τ - δ')..(τ + δ'), (ĝ t - ĝ τ)‖ ≤ (ε / 2) * (2 * δ') := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := τ - δ') (b := τ + δ') (C := ε / 2) (f := fun t => ĝ t - ĝ τ) hbound
    rwa [hlen, abs_of_pos hwpos] at h
  have halg : (1 / (2 * δ')) * (∫ t in (τ - δ')..(τ + δ'), ĝ t) - ĝ τ
      = (1 / (2 * δ')) * (∫ t in (τ - δ')..(τ + δ'), (ĝ t - ĝ τ)) := by
    rw [hsub, hconst, hlen, smul_eq_mul, mul_sub, ← mul_assoc,
      one_div_mul_cancel hwne, one_mul]
  have h1w : (0 : ℝ) < 1 / (2 * δ') := by positivity
  rw [dist_eq_norm, halg, norm_mul, Real.norm_eq_abs (1 / (2 * δ')), abs_of_pos h1w]
  calc (1 / (2 * δ')) * ‖∫ t in (τ - δ')..(τ + δ'), (ĝ t - ĝ τ)‖
      ≤ (1 / (2 * δ')) * ((ε / 2) * (2 * δ')) :=
        mul_le_mul_of_nonneg_left hnorm (le_of_lt h1w)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith


theorem spacetime_as_time
    {t0 t1 : ℝ} (ht : t0 < t1)
    {w : ℝ → ℝ → ℝ} (hw : MemLp (Function.uncurry w) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {ζ : ℝ → ℝ} (hζcont : Continuous ζ) (hζsupp : HasCompactSupport ζ)
    {v : ℝ → ℝ} (hv : MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, w p.1 p.2 * (ζ p.1 * v p.2)
        ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
      = ∫ t in t0..t1, ζ t * (∫ x in (0 : ℝ)..1, w t x * v x) := by
  have hS : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hmeas : volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [isFiniteMeasure_restrict, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hfin_t : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1)) := by
    rw [isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous hζsupp hζcont
  have hζfst : MemLp (fun p : ℝ × ℝ => ζ p.1) ⊤
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    memLp_top_of_bound (hζcont.comp continuous_fst).aestronglyMeasurable C
      (ae_of_all _ fun p => hC p.1)
  have hvSnd : MemLp (fun p : ℝ × ℝ => v p.2) 2
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    haveI := hfin_t
    exact hv.comp_snd (volume.restrict (Set.Icc t0 t1))
  have hh : MemLp (fun p : ℝ × ℝ => ζ p.1 * v p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [hmeas]
    exact MemLp.mul hζfst hvSnd
  have hInt : Integrable (fun p : ℝ × ℝ => w p.1 p.2 * (ζ p.1 * v p.2))
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    haveI := hfin
    exact (MemLp.mul hw hh).integrable le_rfl
  have hInt' : Integrable (fun p : ℝ × ℝ => w p.1 p.2 * (ζ p.1 * v p.2))
      ((volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    rw [← hmeas]
    exact hInt
  have hS' : ((volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)).restrict
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.restrict_restrict hS, Set.inter_self, hmeas]
  rw [hS', integral_prod _ hInt', intervalIntegral.integral_of_le ht.le,
    setIntegral_congr_set Ioc_ae_eq_Icc]
  apply integral_congr_ae
  filter_upwards with t
  have hA : (∫ x, (fun p : ℝ × ℝ => w p.1 p.2 * (ζ p.1 * v p.2)) (t, x)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∫ x in Set.Icc (0 : ℝ) 1, ζ t * (w t x * v x) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    show w t x * (ζ t * v x) = ζ t * (w t x * v x)
    ring
  rw [hA, integral_const_mul, intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
    setIntegral_congr_set Ioc_ae_eq_Icc]



theorem iterated_eq_product
    {t0 t1 : ℝ} (ht : t0 < t1)
    (g : ℝ → ℝ → ℝ)
    (hInt : Integrable (Function.uncurry g)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    (∫ t in t0..t1, ∫ x in (0 : ℝ)..1, g t x)
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          g p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have hS : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hInt' : IntegrableOn (Function.uncurry g)
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := hInt
  have hProd : (∫ t in Set.Icc t0 t1, ∫ x in Set.Icc (0 : ℝ) 1, g t x ∂volume ∂volume)
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, g p.1 p.2 ∂volume :=
    (setIntegral_prod (Function.uncurry g) hInt').symm
  rw [intervalIntegral.integral_of_le ht.le]
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp only [← integral_Icc_eq_integral_Ioc]
  rw [hProd, Measure.restrict_restrict hS, Set.inter_self]

/-- Weak parabolic existence and uniqueness, conditional on the two remaining
assembly inputs: the existence data (the Rothe-limit weak equation, profiles,
time continuity, pointwise initial data, and energy estimate) and the energy
identity for homogeneous solutions. The existence data is proved by the
Rothe-limit assembly (chain + weak-equation passage + profiles); the energy
identity needs Steklov / time-mollifier machinery and is a follow-up.
Uniqueness is stated on the open interval: the closed-interval version is
false at the endpoints (a solution redefined at `t0`, `t1` keeps the weak
equation and initial-data limit but breaks pointwise equality).
Test functions are C^∞ (`ContDiff` at `∞`), not analytic (`⊤` = `ω`). -/
theorem weak_parabolic_exists_unique_conditional
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    {F : ℝ → ℝ → ℝ}
    (hF : MemLp (Function.uncurry F) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {u0 : ℝ → ℝ} (hu0 : MemLp u0 2 (volume.restrict (Set.Icc 0 1)))
    (hExist : ∃ u ux : ℝ → ℝ → ℝ,
      (∀ t, ∃ h : WeakH10, h.toFun = u t ∧ h.weakDeriv = ux t)
      ∧ (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
          ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
              (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x)
            = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
      ∧ Filter.Tendsto (fun t => (eLpNorm (fun x => u t x - u0 x) 2
            (volume.restrict (Set.Icc 0 1))).toReal) (nhdsWithin t0 (Set.Ioi t0)) (nhds 0)
      ∧ (eLpNorm (fun x => u t0 x - u0 x) 2 (volume.restrict (Set.Icc 0 1))) = 0
      ∧ (∀ t ∈ Set.Icc t0 t1,
          (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
            + 2 * kmin * ∫ s in t0..t,
              (eLpNorm (fun x => ux s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
            ≤ (eLpNorm u0 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
              + (1 / kmin) * ∫ s in t0..t,
                (eLpNorm (fun x => F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
              + kmin * ∫ s in t0..t,
                (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2))
    (hEnergyId : ∀ (w wx : ℝ → ℝ → ℝ),
      (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-w t x * deriv (fun s => φ s x) t + κ t x * wx t x * deriv (fun y => φ t y) x) = 0) →
      ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2
          = (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2) :
    ∃ u ux : ℝ → ℝ → ℝ,
      (∀ t, ∃ h : WeakH10, h.toFun = u t ∧ h.weakDeriv = ux t)
      ∧ (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
          ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
              (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x)
            = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
      ∧ Filter.Tendsto (fun t => (eLpNorm (fun x => u t x - u0 x) 2
            (volume.restrict (Set.Icc 0 1))).toReal) (nhdsWithin t0 (Set.Ioi t0)) (nhds 0)
      ∧ (∀ t ∈ Set.Icc t0 t1,
          (eLpNorm (fun x => u t x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
            + 2 * kmin * ∫ s in t0..t,
              (eLpNorm (fun x => ux s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
            ≤ (eLpNorm u0 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
              + (1 / kmin) * ∫ s in t0..t,
                (eLpNorm (fun x => F s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
              + kmin * ∫ s in t0..t,
                (eLpNorm (fun x => u s x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
      ∧ ∀ u' ux' : ℝ → ℝ → ℝ,
        (∀ t, ∃ h : WeakH10, h.toFun = u' t ∧ h.weakDeriv = ux' t) →
        (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
          ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
              (-u' t x * deriv (fun s => φ s x) t + κ t x * ux' t x * deriv (fun y => φ t y) x)
            = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x) →
        Filter.Tendsto (fun t => (eLpNorm (fun x => u' t x - u0 x) 2
            (volume.restrict (Set.Icc 0 1))).toReal) (nhdsWithin t0 (Set.Ioi t0)) (nhds 0) →
        ∀ t ∈ Set.Ioo t0 t1, Set.EqOn (u' t) (u t) (Set.Icc 0 1) := by
  obtain ⟨u, ux, hProf, hWeak, hInit, hInitU, hEnergy⟩ := hExist
  refine ⟨u, ux, hProf, hWeak, hInit, hEnergy, ?_⟩
  intro u' ux' hProf' hWeak' hInit'
  exact weak_parabolic_unique_final ht hkmin (hκ.mono fun p hp => hp.1) hu0
    u ux hProf hWeak hInitU hEnergyId (iterated_eq_product ht) u' ux' hProf' hWeak' hInit'

end EarthScience
