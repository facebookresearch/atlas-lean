/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Importing applications and boundaries for complex L¹ U-moment uniqueness

These consumers and fixtures are independently authored. `source_shape`
reproduces only the theorem type of anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2, entry238, wrapper
`Thm_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero`.
No source proof or extraction utility is copied into this test module.

The square-integrability boundary is an input-space example, not a function
with zero moments. All integral fixtures below have explicit integrability
proofs, so totalized integrals cannot manufacture the examples.
-/

open MeasureTheory Set Polynomial
open scoped ContDiff

@[expose] public section

namespace ChebyshevUniquenessTest

/-- The exact source-shaped importing consumer, including all casts. -/
theorem source_shape (g : ℝ → ℂ)
    (hg : ContinuousOn g (Ioo 0 Real.pi))
    (hgi : IntervalIntegrable g volume 0 Real.pi)
    (hmodes : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
      g θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) = 0) :
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ = 0 :=
  Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
    g hg hgi hmodes

/-- Equal unweighted U moments determine complex angle densities inside. -/
theorem density_unique (f h : ℝ → ℂ)
    (hf : ContinuousOn f (Ioo 0 Real.pi))
    (hh : ContinuousOn h (Ioo 0 Real.pi))
    (hfi : IntervalIntegrable f volume 0 Real.pi)
    (hhi : IntervalIntegrable h volume 0 Real.pi)
    (hm : ∀ j : ℕ,
      (∫ θ in (0 : ℝ)..Real.pi,
        f θ * ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ)) =
      ∫ θ in (0 : ℝ)..Real.pi,
        h θ * ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ)) :
    EqOn f h (Ioo 0 Real.pi) := by
  have hz :=
    Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
    (fun θ => f θ - h θ) (hf.sub hh) (hfi.sub hhi) (fun j => by
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub, hm j, sub_self]
      · exact hfi.mul_continuousOn
          (Complex.continuous_ofReal.comp
            ((Chebyshev.U ℝ (j : ℤ)).continuous.comp
              Real.continuous_cos)).continuousOn
      · exact hhi.mul_continuousOn
          (Complex.continuous_ofReal.comp
            ((Chebyshev.U ℝ (j : ℤ)).continuous.comp
              Real.continuous_cos)).continuousOn)
  exact fun θ hθ => sub_eq_zero.mp (hz θ hθ)

/-- Zero comparison in density uniqueness recovers every source clause. -/
theorem source_from_density (g : ℝ → ℂ)
    (hg : ContinuousOn g (Ioo 0 Real.pi))
    (hgi : IntervalIntegrable g volume 0 Real.pi)
    (hm : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
      g θ * ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0) :
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ = 0 := by
  exact fun θ hθ => density_unique g (fun _ => 0) hg continuousOn_const
    hgi intervalIntegrable_const (fun j => by simpa using hm j) hθ

/-- Sine-square coefficient uniqueness only needs weighted-difference L¹.
In particular, no unweighted integrability of either input is assumed. -/
theorem weighted_unique (f h : ℝ → ℂ)
    (hf : ContinuousOn f (Ioo 0 Real.pi))
    (hh : ContinuousOn h (Ioo 0 Real.pi))
    (hi : IntervalIntegrable
      (fun θ => (f θ - h θ) * (Real.sin θ : ℂ) ^ 2) volume 0 Real.pi)
    (hm : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
      ((f θ - h θ) * (Real.sin θ : ℂ) ^ 2) *
        ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0) :
    EqOn f h (Ioo 0 Real.pi) := by
  have hc := (hf.sub hh).mul
    ((Complex.continuous_ofReal.comp Real.continuous_sin).pow 2).continuousOn
  have hz :=
    Chebyshev.eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
      _ hc hi hm
  intro θ hθ
  exact sub_eq_zero.mp ((mul_eq_zero.mp (hz θ hθ)).resolve_right
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
      (Real.sin_pos_of_mem_Ioo hθ).ne')))

/-- A non-real singleton spike. -/
noncomputable def spike (a : ℝ) (θ : ℝ) : ℂ := by
  classical
  exact if θ = a then Complex.I else 0

/-- Real volume ignores the spike, by its null-singleton property. -/
theorem spike_ae (a : ℝ) : spike a =ᵐ[volume] (fun _ => (0 : ℂ)) := by
  filter_upwards [volume.ae_ne a] with θ hθ
  simp [spike, hθ]

/-- The spike and every moment integrand are genuinely integrable. -/
theorem spike_moments (a : ℝ) :
    IntervalIntegrable (spike a) volume 0 Real.pi ∧
    ∀ j : ℕ,
      IntervalIntegrable (fun θ => spike a θ *
        ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ))
        volume 0 Real.pi ∧
      (∫ θ in (0 : ℝ)..Real.pi, spike a θ *
        ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ)) = 0 := by
  constructor
  · exact intervalIntegrable_const.congr_ae
      (ae_restrict_of_ae (spike_ae a).symm)
  · intro j
    have hzero : (fun θ => spike a θ *
        ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ))
        =ᵐ[volume] (fun _ => (0 : ℂ)) := by
      filter_upwards [spike_ae a] with θ hθ
      simp only [hθ, zero_mul]
    refine ⟨intervalIntegrable_const.congr_ae
      (ae_restrict_of_ae hzero.symm), ?_⟩
    exact intervalIntegral.integral_zero_ae (hzero.mono fun _ hx _ => hx)

/-- Every source premise holds, but the left endpoint is not zero. -/
theorem endpoint_boundary :
    ContinuousOn (spike 0) (Ioo 0 Real.pi) ∧
    IntervalIntegrable (spike 0) volume 0 Real.pi ∧
    (∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi, spike 0 θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0) ∧
    spike 0 0 ≠ 0 := by
  refine ⟨(continuousOn_const (c := (0 : ℂ))).congr ?_, (spike_moments 0).1,
    fun j => ((spike_moments 0).2 j).2, ?_⟩
  · intro θ hθ
    simp [spike, ne_of_gt hθ.1]
  · simp [spike]

/-- Nor can the right endpoint be recovered from the source premises. -/
theorem right_endpoint_boundary :
    ContinuousOn (spike Real.pi) (Ioo 0 Real.pi) ∧
    IntervalIntegrable (spike Real.pi) volume 0 Real.pi ∧
    (∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi, spike Real.pi θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0) ∧
    spike Real.pi Real.pi ≠ 0 := by
  refine ⟨(continuousOn_const (c := (0 : ℂ))).congr ?_,
    (spike_moments Real.pi).1,
    fun j => ((spike_moments Real.pi).2 j).2, ?_⟩
  · intro θ hθ
    simp [spike, ne_of_lt hθ.2]
  · simp [spike]

/-- All moments vanish for an interior spike, but continuity fails there. -/
theorem interior_boundary :
    IntervalIntegrable (spike (Real.pi / 2)) volume 0 Real.pi ∧
    (∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi, spike (Real.pi / 2) θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0) ∧
    spike (Real.pi / 2) (Real.pi / 2) ≠ 0 ∧
    ¬ ContinuousOn (spike (Real.pi / 2)) (Ioo 0 Real.pi) := by
  have hm := spike_moments (Real.pi / 2)
  refine ⟨hm.1, fun j => (hm.2 j).2, by simp [spike], ?_⟩
  intro hc
  have hz := source_shape _ hc hm.1 (fun j => (hm.2 j).2)
    (Real.pi / 2) ⟨Real.pi_div_two_pos, half_lt_self Real.pi_pos⟩
  simp [spike] at hz

/-- A non-real constant density modified only at the left endpoint. -/
noncomputable def endpointDensity (θ : ℝ) : ℂ := Complex.I + spike 0 θ

/-- Equality of all moments comes from the null singleton, not a pointwise
identity assumed as a hypothesis. -/
theorem endpoint_density_data :
    ContinuousOn endpointDensity (Ioo 0 Real.pi) ∧
    IntervalIntegrable endpointDensity volume 0 Real.pi ∧
    ∀ j : ℕ,
      (∫ θ in (0 : ℝ)..Real.pi, Complex.I *
        ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ)) =
      ∫ θ in (0 : ℝ)..Real.pi, endpointDensity θ *
        ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) := by
  refine ⟨continuousOn_const.add endpoint_boundary.1,
    intervalIntegrable_const.add (spike_moments 0).1, ?_⟩
  intro j
  apply intervalIntegral.integral_congr_ae
  filter_upwards [spike_ae 0] with θ hθ _
  simp [endpointDensity, hθ]

/-- Applying density uniqueness to actual nonzero, non-real inputs proves
interior equality but cannot prove equality at the modified endpoint. -/
theorem endpoint_density_application :
    EqOn (fun _ : ℝ => Complex.I) endpointDensity (Ioo 0 Real.pi) ∧
    Complex.I ≠ endpointDensity 0 ∧ Complex.I ≠ 0 ∧ Complex.I.im = 1 := by
  refine ⟨density_unique _ _ continuousOn_const endpoint_density_data.1
    intervalIntegrable_const endpoint_density_data.2.1
    endpoint_density_data.2.2, ?_, Complex.I_ne_zero, rfl⟩
  simp [endpointDensity, spike]

/-- The totalized inverse sine, whose weighted density is simply sine. -/
noncomputable def inverseSine (θ : ℝ) : ℂ := (Real.sin θ : ℂ)⁻¹

/-- The weighted identity also holds at zeros of sine; no cancellation there
is smuggled into the interior uniqueness argument. -/
theorem inverseSine_weight (θ : ℝ) :
    inverseSine θ * (Real.sin θ : ℂ) ^ 2 = (Real.sin θ : ℂ) := by
  unfold inverseSine
  by_cases h : (Real.sin θ : ℂ) = 0
  · simp [h]
  · rw [pow_two, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- Inverse sine is interior-continuous and weighted-integrable. -/
theorem inverseSine_data :
    ContinuousOn inverseSine (Ioo 0 Real.pi) ∧
    IntervalIntegrable (fun θ => inverseSine θ * (Real.sin θ : ℂ) ^ 2)
      volume 0 Real.pi := by
  constructor
  · apply ContinuousOn.inv₀
    · exact (Complex.continuous_ofReal.comp Real.continuous_sin).continuousOn
    · exact fun θ hθ =>
        Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_mem_Ioo hθ).ne'
  · simpa only [inverseSine_weight, Function.comp_def] using
      (Complex.continuous_ofReal.comp Real.continuous_sin).intervalIntegrable
        0 Real.pi

/-- The unweighted inverse sine is not L¹. Comparison with `1 / θ` proves
this assertion; it is not inferred from numerical quadrature. -/
theorem inverseSine_not_integrable :
    ¬ IntervalIntegrable inverseSine volume 0 Real.pi := by
  intro hi
  have hn := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    Real.pi_pos.le).mp hi.norm
  have hinv : IntegrableOn (fun θ : ℝ => θ⁻¹) (Ioo 0 Real.pi) := by
    apply hn.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hs := Real.sin_pos_of_mem_Ioo hθ
    simp only [inverseSine, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hθ.1, abs_of_pos hs]
    simpa only [one_div] using
      one_div_le_one_div_of_le hs (Real.sin_le hθ.1.le)
  have hbad := intervalIntegral.integrableOn_Ioo_rpow_iff
    (s := (-1 : ℝ)) Real.pi_pos
  simp only [Real.rpow_neg_one, lt_self_iff_false, iff_false] at hbad
  exact hbad hinv

/-- The endpoint modification has zero weighted difference everywhere. -/
theorem inverseSine_difference (θ : ℝ) :
    (inverseSine θ - (inverseSine θ + spike 0 θ)) *
      (Real.sin θ : ℂ) ^ 2 = 0 := by
  by_cases hθ : θ = 0
  · subst θ
    simp
  · simp [spike, hθ]

/-- The weighted API applies to two functions outside unweighted L¹. -/
theorem inverseSine_application :
    EqOn inverseSine (fun θ => inverseSine θ + spike 0 θ) (Ioo 0 Real.pi) ∧
    ¬ IntervalIntegrable inverseSine volume 0 Real.pi ∧
    ¬ IntervalIntegrable (fun θ => inverseSine θ + spike 0 θ)
      volume 0 Real.pi := by
  refine ⟨weighted_unique _ _ inverseSine_data.1
    (inverseSine_data.1.add endpoint_boundary.1) ?_ ?_,
    inverseSine_not_integrable, ?_⟩
  · simpa only [inverseSine_difference] using
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 Real.pi)
  · intro j
    simp only [inverseSine_difference, zero_mul, intervalIntegral.integral_zero]
  · intro hi
    apply inverseSine_not_integrable
    simpa only [add_sub_cancel_right] using hi.sub (spike_moments 0).1

/-- A smooth density missed by the first three U moments. -/
noncomputable def finiteSeparator (θ : ℝ) : ℂ :=
  ((Real.sin (4 * θ) * Real.sin θ : ℝ) : ℂ)

/-- The finite-mode separator is smooth, not merely an a.e. spike. -/
theorem finiteSeparator_smooth : ContDiff ℝ ∞ finiteSeparator := by
  simpa only [finiteSeparator, Function.comp_def, Complex.ofRealCLM_apply,
    id_eq] using! Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).mul
        Real.contDiff_sin)

private theorem cosine_integral (n : ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos ((n : ℝ) * θ)) =
      if n = 0 then Real.pi else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, intervalIntegral.integral_comp_mul_left _
      (Int.cast_ne_zero.mpr hn)]
    simp

private theorem sine_product_integral (n : ℤ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin (4 * θ) * Real.sin ((n : ℝ) * θ)) =
      ((if 4 - n = 0 then Real.pi else 0) -
        (if 4 + n = 0 then Real.pi else 0)) / 2 := by
  have heq (θ : ℝ) : Real.sin (4 * θ) * Real.sin ((n : ℝ) * θ) =
      (Real.cos (((4 - n : ℤ) : ℝ) * θ) -
        Real.cos (((4 + n : ℤ) : ℝ) * θ)) / 2 := by
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub,
    cosine_integral, cosine_integral]
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi

/-- The exact all-mode response of the smooth separator. In particular,
modes 0, 1 and 2 vanish and mode 3 is `π / 2`. -/
theorem finiteSeparator_moment (j : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, finiteSeparator θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ)) =
    if j = 3 then ((Real.pi / 2 : ℝ) : ℂ) else 0 := by
  have heq : (∫ θ in (0 : ℝ)..Real.pi, finiteSeparator θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ)) =
      ((∫ θ in (0 : ℝ)..Real.pi,
        Real.sin (4 * θ) *
          Real.sin ((((j : ℤ) + 1 : ℤ) : ℝ) * θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [finiteSeparator]
    rw [← Complex.ofReal_mul]
    congr 1
    calc
      _ = Real.sin (4 * θ) *
          ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) * Real.sin θ) := by ring
      _ = _ := by rw [Chebyshev.U_real_cos]; push_cast; rfl
  rw [heq, sine_product_integral]
  have hplus : (4 : ℤ) + ((j : ℤ) + 1) ≠ 0 := by omega
  have hminus : (4 : ℤ) - ((j : ℤ) + 1) = 0 ↔ j = 3 := by omega
  by_cases hj : j = 3 <;> simp [hplus, hminus, hj]

/-- Integrability is explicit for the separator and every U integrand. -/
theorem finiteSeparator_integrable :
    IntervalIntegrable finiteSeparator volume 0 Real.pi ∧
    ∀ j : ℕ, IntervalIntegrable (fun θ => finiteSeparator θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ))
      volume 0 Real.pi := by
  have hi : IntervalIntegrable finiteSeparator volume 0 Real.pi :=
    finiteSeparator_smooth.continuous.intervalIntegrable 0 Real.pi
  refine ⟨hi, fun j => hi.mul_continuousOn ?_⟩
  exact (Complex.continuous_ofReal.comp
    ((Chebyshev.U ℝ (j : ℤ)).continuous.comp Real.continuous_cos)).continuousOn

/-- Three zero modes do not imply uniqueness, even for a smooth function. -/
theorem finite_mode_boundary :
    (∀ j : ℕ, j < 3 → ∫ θ in (0 : ℝ)..Real.pi, finiteSeparator θ *
      ((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0) ∧
    (∫ θ in (0 : ℝ)..Real.pi, finiteSeparator θ *
      ((Chebyshev.U ℝ 3).eval (Real.cos θ) : ℝ)) =
      ((Real.pi / 2 : ℝ) : ℂ) ∧
    Real.pi / 8 ∈ Ioo (0 : ℝ) Real.pi ∧
    finiteSeparator (Real.pi / 8) ≠ 0 := by
  refine ⟨?_, ?_, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
  · intro j hj
    rw [finiteSeparator_moment, ite_eq_right (by omega)]
  · simpa using finiteSeparator_moment 3
  · rw [finiteSeparator, show 4 * (Real.pi / 8) = Real.pi / 2 by ring,
      Real.sin_pi_div_two, one_mul]
    exact Complex.ofReal_ne_zero.mpr
      (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by linarith [Real.pi_pos])).ne'

/-- The real half-power singularity, viewed in the required complex codomain. -/
noncomputable def halfPower (θ : ℝ) : ℂ :=
  ((θ ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)

/-- This singular function meets the continuity and L¹ input-space clauses.
It is not asserted to have zero U moments. -/
theorem halfPower_data :
    ContinuousOn halfPower (Ioo 0 Real.pi) ∧
    IntervalIntegrable halfPower volume 0 Real.pi := by
  constructor
  · apply Complex.continuous_ofReal.comp_continuousOn
    exact continuousOn_id.rpow_const fun θ hθ => Or.inl hθ.1.ne'
  · have hi : IntervalIntegrable (fun θ : ℝ => θ ^ (-(1 / 2) : ℝ))
        volume 0 Real.pi :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    exact ⟨hi.1.ofReal, hi.2.ofReal⟩

/-- The same complex-valued input is not in L² on the open interval.
The square of its norm has the nonintegrable `θ⁻¹` singularity. -/
theorem halfPower_not_L2 :
    ¬ MemLp halfPower 2 (volume.restrict (Ioo (0 : ℝ) Real.pi)) := by
  intro h
  have hi : IntegrableOn (fun θ => ‖halfPower θ‖ ^ 2) (Ioo 0 Real.pi) :=
    h.integrable_norm_pow (p := 2) (by decide)
  have heq : EqOn (fun θ => ‖halfPower θ‖ ^ 2)
      (fun θ : ℝ => θ ^ (-1 : ℝ)) (Ioo 0 Real.pi) := by
    intro θ hθ
    simp only [halfPower, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hθ.1.le _)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.1.le]
    norm_num
  have hp := (intervalIntegral.integrableOn_Ioo_rpow_iff Real.pi_pos).mp
    (hi.congr_fun heq measurableSet_Ioo)
  norm_num at hp

end ChebyshevUniquenessTest
