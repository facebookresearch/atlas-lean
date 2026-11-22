/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.VariationalEigenvalue

/-!
# Interval baseline for the variational spectrum on the real line

Real nonempty example on `ℝ` with the standard metric, with
`μπ` the volume restricted to `Set.Ioo 0 Real.pi`. It pins the populated
energy, mass and Rayleigh quotient of `Real.cos`, the bottom eigenvalue
`0`, and the `k = 1` upper bound `1` from `span{1, cos}`.
-/

namespace Manifold.VariationalEigenvalueIntervalTest

open Bundle MeasureTheory
open scoped ENNReal NNReal Manifold ContDiff BigOperators

noncomputable section

/-- Restricted volume on the interval `(0, π)`. -/
abbrev μπ : Measure ℝ := volume.restrict (Set.Ioo 0 Real.pi)

/-- Constant `1` as a smooth map on the real line. -/
def constOne : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯ := ContMDiffMap.const (1 : ℝ)

/-- Cosine as a smooth map on the real line. -/
def cosSmooth : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯ :=
  ⟨Real.cos, contMDiff_iff_contDiff.mpr Real.contDiff_cos⟩

private lemma μπ_univ : μπ Set.univ = ENNReal.ofReal Real.pi := by
  have hmeas : MeasurableSet (Set.univ : Set ℝ) := MeasurableSet.univ
  rw [Measure.restrict_apply hmeas, Set.univ_inter, Real.volume_Ioo, sub_zero]

private lemma μπ_pos : 0 < μπ Set.univ := by
  have h : μπ Set.univ = ENNReal.ofReal Real.pi := μπ_univ
  rw [h]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

private lemma μπ_fin : μπ Set.univ < ⊤ := by
  have h : μπ Set.univ = ENNReal.ofReal Real.pi := μπ_univ
  rw [h]
  exact ENNReal.ofReal_lt_top

instance : IsFiniteMeasure μπ := ⟨μπ_fin⟩

private lemma μπ_real_univ : μπ.real Set.univ = Real.pi := by
  have h1 : μπ Set.univ = ENNReal.ofReal Real.pi := μπ_univ
  show (μπ Set.univ).toReal = Real.pi
  rw [h1, ENNReal.toReal_ofReal (le_of_lt Real.pi_pos)]

private lemma fderiv_cos_eq : ∀ x : ℝ,
    fderiv ℝ Real.cos x = (-Real.sin x) • ContinuousLinearMap.id ℝ ℝ := by
  intro (x : ℝ)
  have h1 : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
  have heq : ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin x) =
      (-Real.sin x) • ContinuousLinearMap.id ℝ ℝ := by ext; simp
  have h2 : HasFDerivAt Real.cos
      ((-Real.sin x) • ContinuousLinearMap.id ℝ ℝ) x := heq ▸ h1.hasFDerivAt
  exact h2.fderiv

private lemma norm_fderiv_cos : ∀ x : ℝ,
    ‖fderiv ℝ Real.cos x‖ = |Real.sin x| := by
  intro (x : ℝ)
  have hfd : fderiv ℝ Real.cos x =
      (-Real.sin x) • ContinuousLinearMap.id ℝ ℝ := fderiv_cos_eq x
  have hsmul : ‖(-Real.sin x) • ContinuousLinearMap.id ℝ ℝ‖ =
      ‖-Real.sin x‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ := norm_smul _ _
  have hid : ‖ContinuousLinearMap.id ℝ ℝ‖ = 1 := by simp
  have hneg : ‖-Real.sin x‖ = |Real.sin x| := by
    rw [Real.norm_eq_abs, abs_neg]
  rw [hfd, hsmul, hid, mul_one, hneg]

private lemma enorm_fderiv_cos : ∀ x : ℝ,
    ‖fderiv ℝ Real.cos x‖ₑ = ‖Real.sin x‖ₑ := by
  intro (x : ℝ)
  have hn1 : ‖fderiv ℝ Real.cos x‖ = |Real.sin x| := norm_fderiv_cos x
  have hn2 : ‖Real.sin x‖ = |Real.sin x| := Real.norm_eq_abs _
  have hnn : ‖fderiv ℝ Real.cos x‖₊ = ‖Real.sin x‖₊ :=
    Subtype.ext (hn1.trans hn2.symm)
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]

private lemma sq_energy_cos : ∀ x : ℝ,
    (‖fderiv ℝ Real.cos x‖ₑ ^ 2 : ℝ≥0∞) =
      ENNReal.ofReal (Real.sin x ^ 2) := by
  intro (x : ℝ)
  rw [enorm_fderiv_cos x, Real.enorm_eq_ofReal_abs _,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

private lemma sq_mass_cos : ∀ x : ℝ,
    (‖Real.cos x‖ₑ ^ 2 : ℝ≥0∞) = ENNReal.ofReal (Real.cos x ^ 2) := by
  intro (x : ℝ)
  rw [Real.enorm_eq_ofReal_abs _,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

private lemma integrable_of_bounded_cont {f : ℝ → ℝ} (hf : Continuous f)
    (C : ℝ) (hC : ∀ x : ℝ, ‖f x‖ ≤ C) : Integrable f μπ := by
  have hae : AEStronglyMeasurable f μπ := hf.aestronglyMeasurable
  have hb : ∀ᵐ x ∂μπ, ‖f x‖ ≤ C :=
    Filter.Eventually.of_forall (fun (x : ℝ) => hC x)
  exact Integrable.of_bound hae C hb

private lemma int_cos : Integrable (fun x : ℝ => Real.cos x) μπ := by
  have hc : Continuous (fun x : ℝ => Real.cos x) := Real.continuous_cos
  apply integrable_of_bounded_cont hc 1
  intro (x : ℝ)
  have h1 : ‖Real.cos x‖ = |Real.cos x| := Real.norm_eq_abs _
  have h2 : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
  rw [h1]
  exact h2

private lemma int_sin : Integrable (fun x : ℝ => Real.sin x) μπ := by
  have hc : Continuous (fun x : ℝ => Real.sin x) := Real.continuous_sin
  apply integrable_of_bounded_cont hc 1
  intro (x : ℝ)
  have h1 : ‖Real.sin x‖ = |Real.sin x| := Real.norm_eq_abs _
  have h2 : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  rw [h1]
  exact h2

private lemma int_cos2 : Integrable (fun x : ℝ => Real.cos x ^ 2) μπ := by
  have hc : Continuous (fun x : ℝ => Real.cos x ^ 2) :=
    Real.continuous_cos.pow 2
  apply integrable_of_bounded_cont hc 1
  intro (x : ℝ)
  have hb : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
  have hsq : |Real.cos x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos x)]
  have hn : ‖(Real.cos x ^ 2 : ℝ)‖ = |Real.cos x| ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
  rw [hn]
  exact hsq

private lemma int_sin2 : Integrable (fun x : ℝ => Real.sin x ^ 2) μπ := by
  have hc : Continuous (fun x : ℝ => Real.sin x ^ 2) :=
    Real.continuous_sin.pow 2
  apply integrable_of_bounded_cont hc 1
  intro (x : ℝ)
  have hb : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hsq : |Real.sin x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.sin x)]
  have hn : ‖(Real.sin x ^ 2 : ℝ)‖ = |Real.sin x| ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
  rw [hn]
  exact hsq

private lemma nn_cos2 : 0 ≤ᵐ[μπ] (fun x : ℝ => Real.cos x ^ 2) :=
  Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg (Real.cos x))

private lemma nn_sin2 : 0 ≤ᵐ[μπ] (fun x : ℝ => Real.sin x ^ 2) :=
  Filter.Eventually.of_forall (fun (x : ℝ) => sq_nonneg (Real.sin x))

private lemma boch_cos : (∫ x, Real.cos x ∂μπ) = 0 := by
  have hle : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have h0 : (∫ x, Real.cos x ∂μπ) =
      (∫ x in Set.Ioo (0 : ℝ) Real.pi, Real.cos x ∂volume) := rfl
  have h1 : (∫ x in Set.Ioo (0 : ℝ) Real.pi, Real.cos x ∂volume) =
      (∫ x in (0 : ℝ)..Real.pi, Real.cos x) :=
    (integral_Ioc_eq_integral_Ioo).symm.trans
      (intervalIntegral.integral_of_le hle).symm
  have hval : (∫ x in (0 : ℝ)..Real.pi, Real.cos x) =
      Real.sin Real.pi - Real.sin 0 := integral_cos
  rw [h0, h1, hval, Real.sin_pi, Real.sin_zero, sub_self]

private lemma boch_cos2 : (∫ x, Real.cos x ^ 2 ∂μπ) = Real.pi / 2 := by
  have hle : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have h0 : (∫ x, Real.cos x ^ 2 ∂μπ) =
      (∫ x in Set.Ioo (0 : ℝ) Real.pi, Real.cos x ^ 2 ∂volume) := rfl
  have h1 : (∫ x in Set.Ioo (0 : ℝ) Real.pi, Real.cos x ^ 2 ∂volume) =
      (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 2) :=
    (integral_Ioc_eq_integral_Ioo).symm.trans
      (intervalIntegral.integral_of_le hle).symm
  have hval : (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 2) =
      (Real.cos Real.pi * Real.sin Real.pi - Real.cos 0 * Real.sin 0 +
        Real.pi - 0) / 2 := integral_cos_sq
  rw [h0, h1, hval, Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero]
  ring

private lemma boch_sin2 : (∫ x, Real.sin x ^ 2 ∂μπ) = Real.pi / 2 := by
  have hle : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have h0 : (∫ x, Real.sin x ^ 2 ∂μπ) =
      (∫ x in Set.Ioo (0 : ℝ) Real.pi, Real.sin x ^ 2 ∂volume) := rfl
  have h1 : (∫ x in Set.Ioo (0 : ℝ) Real.pi, Real.sin x ^ 2 ∂volume) =
      (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) :=
    (integral_Ioc_eq_integral_Ioo).symm.trans
      (intervalIntegral.integral_of_le hle).symm
  have hval : (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ 2) =
      (Real.sin 0 * Real.cos 0 - Real.sin Real.pi * Real.cos Real.pi +
        Real.pi - 0) / 2 := integral_sin_sq
  rw [h0, h1, hval, Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero]
  ring

/-- Pins the populated Dirichlet energy of `Real.cos` on `(0, π)`. -/
theorem dirichletEnergy_cos : dirichletEnergy 𝓘(ℝ, ℝ) μπ Real.cos =
    ENNReal.ofReal (Real.pi / 2) := by
  have hvec : dirichletEnergy 𝓘(ℝ, ℝ) μπ Real.cos =
      (∫⁻ x, ‖fderiv ℝ Real.cos x‖ₑ ^ 2 ∂μπ) :=
    dirichletEnergy_vectorSpace μπ Real.cos
  have hfun : (fun x : ℝ => (‖fderiv ℝ Real.cos x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : ℝ => ENNReal.ofReal (Real.sin x ^ 2)) :=
    funext (fun (x : ℝ) => sq_energy_cos x)
  have hof : (∫⁻ x, ENNReal.ofReal (Real.sin x ^ 2) ∂μπ) =
      ENNReal.ofReal (∫ x, Real.sin x ^ 2 ∂μπ) :=
    (ofReal_integral_eq_lintegral_ofReal int_sin2 nn_sin2).symm
  rw [hvec, hfun, hof, boch_sin2]

/-- Pins the populated `L²` mass of `Real.cos` on `(0, π)`. -/
theorem mass_cos : (∫⁻ x, ‖Real.cos x‖ₑ ^ 2 ∂μπ) =
    ENNReal.ofReal (Real.pi / 2) := by
  have hfun : (fun x : ℝ => (‖Real.cos x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : ℝ => ENNReal.ofReal (Real.cos x ^ 2)) :=
    funext (fun (x : ℝ) => sq_mass_cos x)
  have hof : (∫⁻ x, ENNReal.ofReal (Real.cos x ^ 2) ∂μπ) =
      ENNReal.ofReal (∫ x, Real.cos x ^ 2 ∂μπ) :=
    (ofReal_integral_eq_lintegral_ofReal int_cos2 nn_cos2).symm
  rw [hfun, hof, boch_cos2]

/-- Pins the Rayleigh quotient of `Real.cos` to `1`. -/
theorem rayleighQuotient_cos :
    rayleighQuotient 𝓘(ℝ, ℝ) μπ Real.cos = 1 := by
  have hE : dirichletEnergy 𝓘(ℝ, ℝ) μπ Real.cos =
      ENNReal.ofReal (Real.pi / 2) := dirichletEnergy_cos
  have hM : (∫⁻ x, ‖Real.cos x‖ₑ ^ 2 ∂μπ) =
      ENNReal.ofReal (Real.pi / 2) := mass_cos
  have hpos : (0 : ℝ) < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have hne0 : ENNReal.ofReal (Real.pi / 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have hneT : ENNReal.ofReal (Real.pi / 2) ≠ ⊤ :=
    ENNReal.ofReal_lt_top.ne
  unfold rayleighQuotient
  rw [hE, hM]
  exact ENNReal.div_self hne0 hneT

/-- Pins the bottom eigenvalue with all smooth functions to `0`. -/
theorem variationalEigenvalue_zero :
    variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ μπ 0 = 0 := by
  have h1 : ContMDiffMap.const (1 : ℝ) ∈
      (⊤ : Submodule ℝ C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) := Submodule.mem_top
  have hpos : 0 < μπ Set.univ := μπ_pos
  have hfin : μπ Set.univ < ⊤ := μπ_fin
  exact variationalEigenvalue_zero_eq_zero 𝓘(ℝ, ℝ) μπ h1 hpos hfin

/-- Pins the `k = 1` upper bound `1` from `span{1, cos}`. -/
theorem variationalEigenvalue_one_le :
    variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ μπ 1 ≤ 1 := by
  set V : Submodule ℝ C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯ :=
    Submodule.span ℝ (Set.range ![constOne, cosSmooth]) with hVdef
  have hc1 : ∀ x : ℝ, (⇑constOne : ℝ → ℝ) x = 1 := fun (x : ℝ) => rfl
  have hc2 : ∀ x : ℝ, (⇑cosSmooth : ℝ → ℝ) x = Real.cos x :=
    fun (x : ℝ) => rfl
  have hindep : LinearIndependent ℝ ![constOne, cosSmooth] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : ∀ x : ℝ, s + t * Real.cos x = 0 := by
      intro (x : ℝ)
      have hx : ((s • constOne + t • cosSmooth :
          C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) : ℝ → ℝ) x =
          ((0 : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) : ℝ → ℝ) x := by
        rw [hst]
      simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_smul,
        ContMDiffMap.coe_zero, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, hc1, hc2, mul_one] at hx
      exact hx
    have hcos0 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    have hcospi : Real.cos Real.pi = -1 := Real.cos_pi
    have e0 : s + t * 1 = 0 := by rw [← hcos0]; exact h0 0
    have e1 : s + t * (-1) = 0 := by rw [← hcospi]; exact h0 Real.pi
    have hs : s = 0 := by linarith
    have ht : t = 0 := by linarith
    exact ⟨hs, ht⟩
  have hfinrank : Module.finrank ℝ ↥V = 1 + 1 := by
    have hcard : Module.finrank ℝ ↥V = Fintype.card (Fin 2) := by
      rw [hVdef]
      exact finrank_span_eq_card hindep
    rw [hcard, Fintype.card_fin]
  have hVW : V ≤ ⊤ := le_top
  have hrange : Set.range ![constOne, cosSmooth] =
      ({constOne, cosSmooth} : Set C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have key : ∀ u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯, u ∈ V → u ≠ 0 →
      ∃ a b : ℝ, (⇑u = fun x : ℝ => a + b * Real.cos x) ∧
        ((∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μπ) =
          ENNReal.ofReal (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2))) ∧
        (dirichletEnergy 𝓘(ℝ, ℝ) μπ ⇑u =
          ENNReal.ofReal (b ^ 2 * (Real.pi / 2))) ∧
        (0 < Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) := by
    intro (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) (hu : u ∈ V)
      (hune : u ≠ 0)
    have huV : u ∈ Submodule.span ℝ
        (Set.range ![constOne, cosSmooth]) := by rw [← hVdef]; exact hu
    have huV2 : u ∈ Submodule.span ℝ
        ({constOne, cosSmooth} : Set C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) := by
      rw [← hrange]; exact huV
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp huV2
    have hfun : (⇑u : ℝ → ℝ) =
        (fun x : ℝ => a + b * Real.cos x) := by
      rw [← hab]
      funext (x : ℝ)
      simp only [ContMDiffMap.coe_add, ContMDiffMap.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hc1, hc2, mul_one]
    have hab_ne : ¬((a : ℝ) = 0 ∧ (b : ℝ) = 0) := by
      intro hcon
      apply hune
      rw [← hab, hcon.1, hcon.2, zero_smul, zero_smul, add_zero]
    have hexpand : (fun x : ℝ => (a + b * Real.cos x) ^ 2) =
        (fun x : ℝ => a ^ 2 + (2 * a * b * Real.cos x) +
          b ^ 2 * (Real.cos x) ^ 2) :=
      funext (fun (x : ℝ) => by ring)
    have hint1 : Integrable (fun _ : ℝ => a ^ 2) μπ := integrable_const _
    have hint2 : Integrable (fun x : ℝ => 2 * a * b * Real.cos x) μπ :=
      int_cos.const_mul _
    have hint3 : Integrable
        (fun x : ℝ => b ^ 2 * (Real.cos x) ^ 2) μπ :=
      int_cos2.const_mul _
    have hint12 : Integrable
        (fun x : ℝ => a ^ 2 + 2 * a * b * Real.cos x) μπ :=
      hint1.add hint2
    have hint_ab : Integrable
        (fun x : ℝ => (a + b * Real.cos x) ^ 2) μπ := by
      rw [hexpand]
      exact hint12.add hint3
    have hv1 : (∫ _ : ℝ, a ^ 2 ∂μπ) = Real.pi * a ^ 2 := by
      have h : (∫ _ : ℝ, a ^ 2 ∂μπ) =
          μπ.real Set.univ • a ^ 2 := integral_const _
      rw [h, μπ_real_univ, smul_eq_mul]
    have hv2 : (∫ x, 2 * a * b * Real.cos x ∂μπ) = 0 := by
      rw [integral_const_mul, boch_cos, mul_zero]
    have hv3 : (∫ x, b ^ 2 * (Real.cos x) ^ 2 ∂μπ) =
        b ^ 2 * (Real.pi / 2) := by
      rw [integral_const_mul, boch_cos2]
    have hval_ab : (∫ x, (a + b * Real.cos x) ^ 2 ∂μπ) =
        Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2) := by
      rw [hexpand, integral_add hint12 hint3,
        integral_add hint1 hint2, hv1, hv2, hv3, add_zero]
    have hnn_ab : 0 ≤ᵐ[μπ]
        (fun x : ℝ => (a + b * Real.cos x) ^ 2) :=
      Filter.Eventually.of_forall
        (fun (x : ℝ) => sq_nonneg (a + b * Real.cos x))
    have hmass_eq : (∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μπ) =
        ENNReal.ofReal (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) := by
      have hpt : ∀ x : ℝ, (‖⇑u x‖ₑ ^ 2 : ℝ≥0∞) =
          ENNReal.ofReal ((a + b * Real.cos x) ^ 2) := by
        intro (x : ℝ)
        have hx : (⇑u : ℝ → ℝ) x = a + b * Real.cos x := by rw [hfun]
        rw [hx, Real.enorm_eq_ofReal_abs _,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      have hfunEq : (fun x : ℝ => (‖⇑u x‖ₑ ^ 2 : ℝ≥0∞)) =
          (fun x : ℝ => ENNReal.ofReal ((a + b * Real.cos x) ^ 2)) :=
        funext (fun (x : ℝ) => hpt x)
      have hof : (∫⁻ x, ENNReal.ofReal
          ((a + b * Real.cos x) ^ 2) ∂μπ) =
          ENNReal.ofReal (∫ x, (a + b * Real.cos x) ^ 2 ∂μπ) :=
        (ofReal_integral_eq_lintegral_ofReal hint_ab hnn_ab).symm
      rw [hfunEq, hof, hval_ab]
    have hder : ∀ x : ℝ, HasDerivAt (⇑u : ℝ → ℝ)
        (b * (-Real.sin x)) x := by
      intro (x : ℝ)
      have hcos : HasDerivAt Real.cos (-Real.sin x) x :=
        Real.hasDerivAt_cos x
      have hmul : HasDerivAt (fun y : ℝ => b * Real.cos y)
          (b * (-Real.sin x)) x := hcos.const_mul b
      have hadd : HasDerivAt (fun y : ℝ => a + b * Real.cos y)
          (b * (-Real.sin x)) x := hmul.const_add a
      rw [hfun]
      exact hadd
    have hfd : ∀ x : ℝ, fderiv ℝ (⇑u : ℝ → ℝ) x =
        (b * (-Real.sin x)) • ContinuousLinearMap.id ℝ ℝ := by
      intro (x : ℝ)
      have heq : ContinuousLinearMap.toSpanSingleton ℝ (b * (-Real.sin x)) =
          (b * (-Real.sin x)) • ContinuousLinearMap.id ℝ ℝ := by
        ext; simp
      have h2 : HasFDerivAt (⇑u : ℝ → ℝ)
          ((b * (-Real.sin x)) • ContinuousLinearMap.id ℝ ℝ) x :=
        heq ▸ (hder x).hasFDerivAt
      exact h2.fderiv
    have hsqE : ∀ x : ℝ, (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞) =
        ENNReal.ofReal (b ^ 2 * (Real.sin x) ^ 2) := by
      intro (x : ℝ)
      have hn : ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ =
          |b * (-Real.sin x)| := by
        rw [hfd x, norm_smul, Real.norm_eq_abs]
        simp
      have hnn : ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖₊ =
          ‖(b * (-Real.sin x) : ℝ)‖₊ :=
        Subtype.ext (hn.trans (Real.norm_eq_abs _).symm)
      have he : (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ : ℝ≥0∞) =
          ‖(b * (-Real.sin x) : ℝ)‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]
      rw [he, Real.enorm_eq_ofReal_abs _,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      congr 1
      ring
    have hintE : Integrable
        (fun x : ℝ => b ^ 2 * (Real.sin x) ^ 2) μπ :=
      int_sin2.const_mul _
    have hnnE : 0 ≤ᵐ[μπ]
        (fun x : ℝ => b ^ 2 * (Real.sin x) ^ 2) :=
      Filter.Eventually.of_forall (fun (x : ℝ) => by
        apply mul_nonneg (sq_nonneg _)
        exact sq_nonneg _)
    have hvE : (∫ x, b ^ 2 * (Real.sin x) ^ 2 ∂μπ) =
        b ^ 2 * (Real.pi / 2) := by
      rw [integral_const_mul, boch_sin2]
    have henergy_eq : dirichletEnergy 𝓘(ℝ, ℝ) μπ ⇑u =
        ENNReal.ofReal (b ^ 2 * (Real.pi / 2)) := by
      have hvec : dirichletEnergy 𝓘(ℝ, ℝ) μπ ⇑u =
          (∫⁻ x, ‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 ∂μπ) :=
        dirichletEnergy_vectorSpace μπ ⇑u
      have hfunE : (fun x : ℝ =>
          (‖fderiv ℝ (⇑u : ℝ → ℝ) x‖ₑ ^ 2 : ℝ≥0∞)) =
          (fun x : ℝ => ENNReal.ofReal (b ^ 2 * (Real.sin x) ^ 2)) :=
        funext (fun (x : ℝ) => hsqE x)
      have hof : (∫⁻ x, ENNReal.ofReal
          (b ^ 2 * (Real.sin x) ^ 2) ∂μπ) =
          ENNReal.ofReal (∫ x, b ^ 2 * (Real.sin x) ^ 2 ∂μπ) :=
        (ofReal_integral_eq_lintegral_ofReal hintE hnnE).symm
      rw [hvec, hfunE, hof, hvE]
    have hpos : 0 < Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2) := by
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      have hhalf : (0 : ℝ) < Real.pi / 2 :=
        div_pos Real.pi_pos (by norm_num)
      have hnn1 : (0 : ℝ) ≤ Real.pi * a ^ 2 :=
        mul_nonneg (le_of_lt hpi) (sq_nonneg _)
      have hnn2 : (0 : ℝ) ≤ b ^ 2 * (Real.pi / 2) :=
        mul_nonneg (sq_nonneg _) (le_of_lt hhalf)
      by_cases ha : a = 0
      · have hb : b ≠ 0 := fun hb => hab_ne ⟨ha, hb⟩
        have hp1 : (0 : ℝ) < b ^ 2 * (Real.pi / 2) :=
          mul_pos (sq_pos_of_ne_zero hb) hhalf
        exact add_pos_of_nonneg_of_pos hnn1 hp1
      · have hp0 : (0 : ℝ) < Real.pi * a ^ 2 :=
          mul_pos hpi (sq_pos_of_ne_zero ha)
        exact add_pos_of_pos_of_nonneg hp0 hnn2
    exact ⟨a, b, hfun, hmass_eq, henergy_eq, hpos⟩
  have hmass : ∀ u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯, u ∈ V → u ≠ 0 →
      0 < (∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μπ) ∧
        (∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μπ) < ⊤ := by
    intro (u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) (hu : u ∈ V)
      (hune : u ≠ 0)
    obtain ⟨a, b, hfun, hmass_eq, henergy_eq, hpos⟩ := key u hu hune
    exact ⟨by rw [hmass_eq]; exact ENNReal.ofReal_pos.mpr hpos,
      by rw [hmass_eq]; exact ENNReal.ofReal_lt_top⟩
  have hsup : (⨆ u : ↥V, ⨆ _ : u ≠ 0,
      rayleighQuotient 𝓘(ℝ, ℝ) μπ ⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)) ≤ 1 := by
    apply iSup_le
    intro u
    apply iSup_le
    intro (h : u ≠ 0)
    have hu : (u.val : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) ∈ V := u.property
    have hune : (u.val : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) ≠ 0 := by
      intro h0
      apply h
      apply Subtype.ext
      simpa using h0
    obtain ⟨a, b, hfun, hmass_eq, henergy_eq, hpos⟩ := key u.val hu hune
    have hE : dirichletEnergy 𝓘(ℝ, ℝ) μπ ⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) =
        ENNReal.ofReal (b ^ 2 * (Real.pi / 2)) := henergy_eq
    have hM : (∫⁻ x, ‖⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂μπ) =
        ENNReal.ofReal (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) := hmass_eq
    have hMpos : (0 : ℝ) < Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2) := hpos
    have hre : b ^ 2 * (Real.pi / 2) ≤
        Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2) := by
      apply le_add_of_nonneg_left
      exact mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)
    have hleR : ENNReal.ofReal (b ^ 2 * (Real.pi / 2)) ≤
        ENNReal.ofReal (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) :=
      ENNReal.ofReal_le_ofReal hre
    have hne0 : ENNReal.ofReal
        (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hMpos)
    have hneT : ENNReal.ofReal
        (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) ≠ ⊤ :=
      ENNReal.ofReal_lt_top.ne
    have hrw : rayleighQuotient 𝓘(ℝ, ℝ) μπ
        ⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯) =
        ENNReal.ofReal (b ^ 2 * (Real.pi / 2)) /
          ENNReal.ofReal (Real.pi * a ^ 2 + b ^ 2 * (Real.pi / 2)) := by
      unfold rayleighQuotient
      rw [hE, hM]
    rw [hrw, ENNReal.div_le_iff hne0 hneT, one_mul]
    exact hleR
  have hle : variationalEigenvalue 𝓘(ℝ, ℝ) ⊤ μπ 1 ≤
      (⨆ u : ↥V, ⨆ _ : u ≠ 0,
        rayleighQuotient 𝓘(ℝ, ℝ) μπ
          ⇑(u : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, ℝ), ℝ⟯)) :=
    variationalEigenvalue_le_iSup 𝓘(ℝ, ℝ) μπ 1 hVW hfinrank hmass
  exact le_trans hle hsup

end

end Manifold.VariationalEigenvalueIntervalTest
