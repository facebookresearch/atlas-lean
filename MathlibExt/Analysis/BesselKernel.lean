/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_ArchBessel.lean`,
`Theorems/Thm_LanglandsTunnell_ArchBessel_exists_besselKernel_ne_zero.lean`,
`Theorems/Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel_
and_hasDerivAt_deriv_besselKernel.lean`,
`Theorems/Thm_LanglandsTunnell_ArchBessel_hasDerivAt_besselKernel.lean`,
`Theorems/Thm_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow.lean`,
`Theorems/Thm_LanglandsTunnell_ArchBessel_mellin_besselKernel_eq_mul_Gamma_mul_Gamma.lean`,
`Theorems/Thm_LanglandsTunnell_ArchBessel_mul_besselKernel_eq_mul_sub.lean`
and their `P2M/Sol` proofs
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

@[expose] public section

open MeasureTheory Set Filter

namespace ArchBessel

/-- The archimedean Bessel kernel, defined by an integral over the
positive real axis. -/
noncomputable def besselKernel (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))

theorem besselKernel_def (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ),
      (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1)) :=
  rfl

/-- The Bessel integrand is integrable on the positive axis. -/
theorem integrableOn_exp_neg_mul_add_inv_mul_cpow (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn
      (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) (Set.Ioi 0) := by
  set a : ℝ := ν.re with ha

  set m : ℕ := ⌈-a⌉₊ + 1 with hm
  have hma : -1 < (m : ℝ) + a - 1 := by
    rw [hm]; have := Nat.le_ceil (-a); push_cast; linarith
  have hx2 : 0 < x / 2 := by linarith

  set C : ℝ := (m.factorial : ℝ) * (2 / x) ^ m with hC
  have hC0 : 0 ≤ C := by positivity
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ => C * (t ^ ((m : ℝ) + a - 1) * Real.exp (-(x /
    2) * t ^ (1 : ℝ)))) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hma one_pos hx2).const_mul C

  have hcont : ContinuousOn (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν -
    1))) (Set.Ioi 0) := by
    intro t ht
    have ht0 : t ≠ 0 := (ne_of_gt ht)
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ (Complex.continuousAt_ofReal_cpow_const t (ν - 1) (Or.inr ht0))
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    refine Real.continuous_exp.continuousAt.comp ?_
    exact ((continuousAt_const.mul (continuousAt_id.add (continuousAt_inv₀ ht0))).div_const _).neg
  rw [MeasureTheory.IntegrableOn]
  refine MeasureTheory.Integrable.mono' hg.integrable (hcont.aestronglyMeasurable
    measurableSet_Ioi) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ?_
  have ht' : 0 < t := ht

  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    Complex.norm_cpow_eq_rpow_re_of_pos ht',
    Complex.sub_re, Complex.one_re, ← ha, Real.rpow_one]

  have hsplit : Real.exp (-(x * (t + t⁻¹) / 2)) = Real.exp (-(x / 2) * t) * Real.exp (-((x / 2) /
    t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hu : 0 < (x / 2) / t := by positivity
  have hsing : Real.exp (-((x / 2) / t)) ≤ (m.factorial : ℝ) * (2 / x) ^ m * t ^ m := by
    have h1 := Real.pow_div_factorial_le_exp ((x / 2) / t) hu.le m
    have hfac : (0 : ℝ) < m.factorial := by positivity
    rw [div_le_iff₀ hfac] at h1
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]

    have h2 : ((x / 2) / t) ^ m * ((2 / x) ^ m * t ^ m) = 1 := by
      rw [← mul_pow, ← mul_pow]; rw [show (x / 2) / t * (2 / x * t) = 1 by field_simp]; simp
    calc (1 : ℝ) = ((x / 2) / t) ^ m * ((2 / x) ^ m * t ^ m) := h2.symm
      _ ≤ (Real.exp ((x / 2) / t) * m.factorial) * ((2 / x) ^ m * t ^ m) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (m.factorial : ℝ) * (2 / x) ^ m * t ^ m * Real.exp ((x / 2) / t) := by ring
  have hpow : t ^ m * t ^ (a - 1) = t ^ ((m : ℝ) + a - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht']; congr 1; ring
  rw [hsplit]
  calc Real.exp (-(x / 2) * t) * Real.exp (-((x / 2) / t)) * t ^ (a - 1)
      ≤ Real.exp (-(x / 2) * t) * ((m.factorial : ℝ) * (2 / x) ^ m * t ^ m) * t ^ (a - 1) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsing (Real.exp_pos _).le) ?_
        exact Real.rpow_nonneg ht'.le _
    _ = C * ((t ^ m * t ^ (a - 1)) * Real.exp (-(x / 2) * t)) := by rw [hC]; ring
    _ = C * (t ^ ((m : ℝ) + a - 1) * Real.exp (-(x / 2) * t)) := by rw [hpow]

namespace DerivAux

private noncomputable def g (x t : ℝ) : ℝ := Real.exp (-(x * (t + t⁻¹) / 2))

private noncomputable def E (x t : ℝ) : ℂ := ((g x t : ℝ) : ℂ)

private theorem g_pos (x t : ℝ) : 0 < g x t := Real.exp_pos _

private theorem besselKernel_eq (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), E x t * ((t : ℂ) ^ (ν - 1)) := rfl

private theorem integrableOn_E_mul_cpow (μ : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => E x t * ((t : ℂ) ^ (μ - 1))) (Ioi 0) :=
  integrableOn_exp_neg_mul_add_inv_mul_cpow μ x hx

private theorem norm_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖E x t * (t : ℂ) ^ ν‖ = g x t * t ^ ν.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, E, Complex.norm_real,
    Real.norm_of_nonneg (g_pos x t).le]

private theorem g_mono (x x' t : ℝ) (hxx' : x ≤ x') (ht : 0 < t) : g x' t ≤ g x t := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ t + t⁻¹ := by positivity
  nlinarith

private theorem hasDerivAt_g (x t : ℝ) :
    HasDerivAt (fun y => g y t) (g x t * (-((t + t⁻¹) / 2))) x := by
  unfold g
  have h1 : HasDerivAt (fun y : ℝ => -(y * (t + t⁻¹) / 2)) (-(1 * (t + t⁻¹) / 2)) x :=
    (((hasDerivAt_id x).mul_const (t + t⁻¹)).div_const 2).neg
  have h2 := h1.exp
  convert h2 using 1 <;> ring

private noncomputable def F' (ν : ℂ) (x t : ℝ) : ℂ :=
  -((E x t * (t : ℂ) ^ (ν - 1 - 1) + E x t * (t : ℂ) ^ (ν + 1 - 1)) / 2)

private theorem hasDerivAt_F (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => E y t * (t : ℂ) ^ (ν - 1)) (F' ν x t) x := by
  have hE : HasDerivAt (fun y : ℝ => E y t) ((g x t * (-((t + t⁻¹) / 2)) : ℝ) : ℂ) x :=
    (hasDerivAt_g x t).ofReal_comp
  have h := hE.mul_const ((t : ℂ) ^ (ν - 1))
  refine h.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : (t : ℂ) ^ (ν + 1 - 1) = (t : ℂ) ^ ν := by rw [add_sub_cancel_right]
  have e2 : (t : ℂ) ^ (ν - 1 - 1) = (t : ℂ) ^ ν / (t : ℂ) ^ (2 : ℕ) := by
    rw [show ν - 1 - 1 = ν - 2 by ring, Complex.cpow_sub _ _ ht0, Complex.cpow_two]
  have e3 : (t : ℂ) ^ (ν - 1) = (t : ℂ) ^ ν / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
  simp only [F', E, e1, e2, e3]
  push_cast
  field_simp
  ring

private theorem main (ν : ℂ) (x₀ : ℝ) (hx₀ : 0 < x₀) :
    HasDerivAt (fun x : ℝ => besselKernel ν x)
      (-(besselKernel (ν - 1) x₀ + besselKernel (ν + 1) x₀) / 2) x₀ := by
  have hx2 : 0 < x₀ / 2 := half_pos hx₀
  have hs : Ioi (x₀ / 2) ∈ nhds x₀ := Ioi_mem_nhds (by linarith)
  let bound : ℝ → ℝ := fun t =>
    (‖E (x₀ / 2) t * (t : ℂ) ^ (ν - 1 - 1)‖ + ‖E (x₀ / 2) t * (t : ℂ) ^ (ν + 1 - 1)‖) / 2
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (fun t : ℝ => E x t * (t : ℂ) ^ (ν - 1)) (volume.restrict (Ioi 0)) := by
    filter_upwards [hs] with x hx
    exact (integrableOn_E_mul_cpow ν x (lt_trans hx2 hx)).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => E x₀ t * (t : ℂ) ^ (ν - 1)) (volume.restrict (Ioi 0)) :=
    integrableOn_E_mul_cpow ν x₀ hx₀
  have hA : ∀ x : ℝ, 0 < x →
      Integrable (fun t : ℝ => E x t * (t : ℂ) ^ (ν - 1 - 1)) (volume.restrict (Ioi 0)) :=
    fun x hx => integrableOn_E_mul_cpow (ν - 1) x hx
  have hB : ∀ x : ℝ, 0 < x →
      Integrable (fun t : ℝ => E x t * (t : ℂ) ^ (ν + 1 - 1)) (volume.restrict (Ioi 0)) :=
    fun x hx => integrableOn_E_mul_cpow (ν + 1) x hx
  have hF'_int : Integrable (F' ν x₀) (volume.restrict (Ioi 0)) :=
    (((hA x₀ hx₀).add (hB x₀ hx₀)).div_const 2).neg
  have hF'_meas : AEStronglyMeasurable (F' ν x₀) (volume.restrict (Ioi 0)) :=
    hF'_int.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Ioi (x₀ / 2), ‖F' ν x t‖ ≤ bound t :=
    by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x hx
    have ht' : 0 < t := ht
    have hxle : x₀ / 2 ≤ x := le_of_lt hx
    simp only [F', bound, norm_neg, norm_div, Complex.norm_ofNat]
    gcongr
    calc ‖E x t * (t : ℂ) ^ (ν - 1 - 1) + E x t * (t : ℂ) ^ (ν + 1 - 1)‖
        ≤ ‖E x t * (t : ℂ) ^ (ν - 1 - 1)‖ + ‖E x t * (t : ℂ) ^ (ν + 1 - 1)‖ := norm_add_le _ _
      _ ≤ ‖E (x₀ / 2) t * (t : ℂ) ^ (ν - 1 - 1)‖ + ‖E (x₀ / 2) t * (t : ℂ) ^ (ν + 1 - 1)‖ := by
          rw [norm_E_mul_cpow _ _ _ ht', norm_E_mul_cpow _ _ _ ht', norm_E_mul_cpow _ _ _ ht',
            norm_E_mul_cpow _ _ _ ht']
          gcongr
          · exact g_mono _ _ _ hxle ht'
          · exact g_mono _ _ _ hxle ht'
  have bound_integrable : Integrable bound (volume.restrict (Ioi 0)) :=
    ((hA _ hx2).norm.add (hB _ hx2).norm).div_const 2
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ x ∈ Ioi (x₀ / 2),
      HasDerivAt (fun y : ℝ => E y t * (t : ℂ) ^ (ν - 1)) (F' ν x t) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro x _
    exact hasDerivAt_F ν x t ht
  have H := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff).2
  have hval : (∫ t, F' ν x₀ t ∂(volume.restrict (Ioi (0 : ℝ)))) =
      -(besselKernel (ν - 1) x₀ + besselKernel (ν + 1) x₀) / 2 := by
    show (∫ t in Ioi (0 : ℝ), F' ν x₀ t) = _
    unfold F'
    rw [integral_neg, integral_div, integral_add (hA x₀ hx₀) (hB x₀ hx₀), besselKernel_eq,
      besselKernel_eq, neg_div]
  rw [hval] at H
  exact H

end DerivAux

/-- First derivative of the Bessel kernel. -/
theorem hasDerivAt_besselKernel (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x)
      (-(besselKernel (ν - 1) x + besselKernel (ν + 1) x) / 2) x :=
  DerivAux.main ν x hx

namespace IndexRecAux

private noncomputable def g (x t : ℝ) : ℝ := Real.exp (-(x * (t + t⁻¹) / 2))

private noncomputable def E (x t : ℝ) : ℂ := ((g x t : ℝ) : ℂ)

private theorem besselKernel_eq (ν : ℂ) (x : ℝ) :
    besselKernel ν x = ∫ t in Ioi (0 : ℝ), E x t * ((t : ℂ) ^ (ν - 1)) := rfl

private theorem integrableOn_E_mul_cpow (μ : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => E x t * ((t : ℂ) ^ (μ - 1))) (Ioi 0) :=
  integrableOn_exp_neg_mul_add_inv_mul_cpow μ x hx

private theorem hasDerivAt_g (x t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s => g x s) (g x t * (-(x * (1 - (t ^ 2)⁻¹) / 2))) t := by
  unfold g
  have h1 : HasDerivAt (fun s : ℝ => s + s⁻¹) (1 + (-(t ^ 2)⁻¹)) t :=
    (hasDerivAt_id t).add (hasDerivAt_inv ht)
  have h2 : HasDerivAt (fun s : ℝ => -(x * (s + s⁻¹) / 2)) (-(x * (1 + (-(t ^ 2)⁻¹)) / 2)) t :=
    ((h1.const_mul x).div_const 2).neg
  have h3 := h2.exp
  convert h3 using 1 <;> ring

private theorem hasDerivAt_ofReal_cpow (ν : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (s : ℂ) ^ ν) (ν * (t : ℂ) ^ (ν - 1)) t := by
  have h0 : (id (t : ℂ)) ∈ Complex.slitPlane := by
    simpa [Complex.ofReal_mem_slitPlane] using ht
  have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := ν) h0).comp_ofReal
  simpa using h

private noncomputable def F' (ν : ℂ) (x t : ℝ) : ℂ :=
  ν * (E x t * (t : ℂ) ^ (ν - 1)) - (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1))
    + (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν - 1 - 1))

private theorem hasDerivAt_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => E x s * (s : ℂ) ^ ν) (F' ν x t) t := by
  have hE : HasDerivAt (fun s : ℝ => E x s) ((g x t * (-(x * (1 - (t ^ 2)⁻¹) / 2)) : ℝ) : ℂ) t :=
    (hasDerivAt_g x t ht.ne').ofReal_comp
  have h := hE.mul (hasDerivAt_ofReal_cpow ν t ht)
  refine h.congr_deriv ?_
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have e1 : (t : ℂ) ^ (ν + 1 - 1) = (t : ℂ) ^ ν := by rw [add_sub_cancel_right]
  have e2 : (t : ℂ) ^ (ν - 1 - 1) = (t : ℂ) ^ ν / (t : ℂ) ^ (2 : ℕ) := by
    rw [show ν - 1 - 1 = ν - 2 by ring, Complex.cpow_sub _ _ ht0, Complex.cpow_two]
  have e3 : (t : ℂ) ^ (ν - 1) = (t : ℂ) ^ ν / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ ht0, Complex.cpow_one]
  simp only [F', E, e1, e2, e3]
  push_cast
  field_simp
  ring

private theorem g_pos (x t : ℝ) : 0 < g x t := Real.exp_pos _

private theorem norm_E_mul_cpow (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖E x t * (t : ℂ) ^ ν‖ = g x t * t ^ ν.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, E, Complex.norm_real,
    Real.norm_of_nonneg (g_pos x t).le]

private theorem g_le_exp_neg_mul (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    g x t ≤ Real.exp (-(x / 2) * t) := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x * t⁻¹ := by positivity
  nlinarith

private theorem g_le_exp_neg_mul_inv (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    g x t ≤ Real.exp (-(x / 2) * t⁻¹) := by
  unfold g
  apply Real.exp_le_exp.mpr
  have : 0 ≤ x * t := by positivity
  nlinarith

private theorem tendsto_atTop (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => E x t * (t : ℂ) ^ ν) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ν.re (x / 2) (by
    positivity))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_E_mul_cpow ν x t ht, mul_comm]
  exact mul_le_mul_of_nonneg_left (g_le_exp_neg_mul x t hx ht) (Real.rpow_nonneg ht.le _)

private theorem tendsto_nhdsGT_zero (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => E x t * (t : ℂ) ^ ν) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-ν.re) (x / 2) (by positivity)).comp
    tendsto_inv_nhdsGT_zero
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  rw [norm_E_mul_cpow ν x t ht', Function.comp_apply, mul_comm]
  have hr : t ^ ν.re = (t⁻¹) ^ (-ν.re) := by
    rw [Real.rpow_neg (inv_nonneg.mpr ht'.le), Real.inv_rpow ht'.le, inv_inv]
  rw [hr]
  exact mul_le_mul_of_nonneg_left (g_le_exp_neg_mul_inv x t hx ht')
    (Real.rpow_nonneg (inv_nonneg.mpr ht'.le) _)

private theorem integral_F' (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), F' ν x t =
      ν * besselKernel ν x - (x : ℂ) / 2 * besselKernel (ν + 1) x
        + (x : ℂ) / 2 * besselKernel (ν - 1) x := by
  have h1 : Integrable (fun t : ℝ => ν * (E x t * (t : ℂ) ^ (ν - 1))) (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow ν x hx).const_mul ν
  have h2 : Integrable (fun t : ℝ => (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow (ν + 1) x hx).const_mul _
  have h3 : Integrable (fun t : ℝ => (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν - 1 - 1)))
      (volume.restrict (Ioi 0)) :=
    (integrableOn_E_mul_cpow (ν - 1) x hx).const_mul _
  have h12 : Integrable (fun t : ℝ => ν * (E x t * (t : ℂ) ^ (ν - 1))
      - (x : ℂ) / 2 * (E x t * (t : ℂ) ^ (ν + 1 - 1))) (volume.restrict (Ioi 0)) := h1.sub h2
  unfold F'
  rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul,
    integral_const_mul, besselKernel_eq, besselKernel_eq, besselKernel_eq]

private theorem main (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) := by
  classical
  let F : ℝ → ℂ := fun t => if 0 < t then E x t * (t : ℂ) ^ ν else 0
  have hFeq : EqOn F (fun t => E x t * (t : ℂ) ^ ν) (Ioi 0) := fun t ht => ite_eq_left ht
  have hF0 : F 0 = 0 := ite_eq_right (lt_irrefl 0)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (F' ν x t) t := by
    intro t ht
    exact (hasDerivAt_E_mul_cpow ν x t ht).congr_of_eventuallyEq
      (eventuallyEq_of_mem (Ioi_mem_nhds ht) hFeq)
  have hint : IntegrableOn (F' ν x) (Ioi 0) := by
    have h1 := (integrableOn_E_mul_cpow ν x hx).const_mul ν
    have h2 := (integrableOn_E_mul_cpow (ν + 1) x hx).const_mul ((x : ℂ) / 2)
    have h3 := (integrableOn_E_mul_cpow (ν - 1) x hx).const_mul ((x : ℂ) / 2)
    exact (h1.sub h2).add h3
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hF0]
    exact (tendsto_nhdsGT_zero ν x hx).congr' (eventuallyEq_of_mem self_mem_nhdsWithin hFeq).symm
  have hlim : Tendsto F atTop (nhds 0) :=
    (tendsto_atTop ν x hx).congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) hFeq).symm
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [hF0, sub_zero, integral_F' ν x hx] at hFTC
  linear_combination hFTC

end IndexRecAux

/-- Index recurrence for the Bessel kernel. -/
theorem mul_besselKernel_eq_mul_sub (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    ν * besselKernel ν x = (x : ℂ) / 2 * (besselKernel (ν + 1) x - besselKernel (ν - 1) x) :=
  IndexRecAux.main ν x hx

namespace MellinK

private theorem integrable_of_integral_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {E :
  Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → E} (h : ∫ x, f x ∂μ ≠ 0) : Integrable f μ :=
      by
  by_contra hf
  exact h (integral_undef hf)

private theorem integrableOn_cpow_mul_exp_neg_mul {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by
    rw [one_div]; exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'))))
      (Complex.Gamma_ne_zero_of_re_pos ha)

private theorem integrableOn_rpow_mul_exp_neg_mul {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  exact mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne'

private theorem integral_cpow_mul_exp_neg_mul_sq {a : ℂ} {y : ℝ} (ha : 0 < a.re) (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2)) =
      (1 / 2 : ℂ) * ((1 / (y : ℂ)) ^ a * Complex.Gamma a) := by
  have hsub := integral_comp_rpow_Ioi
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * Complex.exp (-((y : ℂ) * (u : ℂ)))) (p := 2) two_ne_zero
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hy] at hsub
  have hcongr : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        ((((x ^ (2 : ℝ)) : ℝ) : ℂ) ^ (a - 1) * Complex.exp (-((y : ℂ) * (((x ^ (2 : ℝ)) : ℝ) :
          ℂ)))) =
      ∫ x in Ioi (0 : ℝ), (2 : ℂ) * ((x : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (x : ℂ) ^
        2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : 0 < x := hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have e1 : ((((x ^ (2 : ℝ)) : ℝ) : ℂ)) ^ (a - 1) = (x : ℂ) ^ ((2 : ℂ) * (a - 1)) := by
      rw [← Complex.cpow_mul_ofReal_nonneg hx.le]; push_cast; ring_nf
    have e2 : ((((x ^ (2 : ℝ)) : ℝ) : ℂ)) = (x : ℂ) ^ 2 := by
      rw [Real.rpow_two]; push_cast; ring
    have e3 : |(2 : ℝ)| * x ^ ((2 : ℝ) - 1) = 2 * x := by norm_num
    rw [e3, e1, e2, Complex.real_smul]
    push_cast
    have e4 : (x : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1)) = (x : ℂ) ^ (2 * a - 1) := by
      rw [show (x : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1)) = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ ((2 : ℂ) *
        (a - 1)) by
        rw [Complex.cpow_one], ← Complex.cpow_add _ _ hx0]
      congr 1; ring
    calc (2 : ℂ) * (x : ℂ) * ((x : ℂ) ^ ((2 : ℂ) * (a - 1)) * Complex.exp (-((y : ℂ) * (x : ℂ) ^
      2)))
        = 2 * (((x : ℂ) * (x : ℂ) ^ ((2 : ℂ) * (a - 1))) * Complex.exp (-((y : ℂ) * (x : ℂ) ^ 2)))
          := by ring
      _ = _ := by rw [e4]
  rw [hcongr, integral_const_mul] at hsub
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  calc ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))
      = (1 / 2 : ℂ) * ((2 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * a - 1) * Complex.exp (-((y : ℂ)
        * (t : ℂ) ^ 2))) := by
        field_simp
    _ = (1 / 2 : ℂ) * ((1 / (y : ℂ)) ^ a * Complex.Gamma a) := by rw [hsub]

private theorem integral_rpow_mul_exp_neg_mul_sq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * a - 1) * Real.exp (-(y * t ^ 2)) = (1 / 2) * ((1 / y) ^ a *
      Real.Gamma a) := by
  have hsub := integral_comp_rpow_Ioi
    (fun u : ℝ => u ^ (a - 1) * Real.exp (-(y * u))) (p := 2) two_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hy] at hsub
  have hcongr : ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        ((x ^ (2 : ℝ)) ^ (a - 1) * Real.exp (-(y * x ^ (2 : ℝ)))) =
      ∫ x in Ioi (0 : ℝ), 2 * (x ^ (2 * a - 1) * Real.exp (-(y * x ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : 0 < x := hx
    have e1 : (x ^ (2 : ℝ)) ^ (a - 1) = x ^ (2 * (a - 1)) := by rw [← Real.rpow_mul hx.le]
    have e2 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_two x
    have e3 : |(2 : ℝ)| * x ^ ((2 : ℝ) - 1) = 2 * x := by norm_num
    rw [e3, e1, e2, smul_eq_mul]
    have e4 : x * x ^ (2 * (a - 1)) = x ^ (2 * a - 1) := by
      rw [show x * x ^ (2 * (a - 1)) = x ^ (1 : ℝ) * x ^ (2 * (a - 1)) by rw [Real.rpow_one],
        ← Real.rpow_add hx]
      congr 1; ring
    calc 2 * x * (x ^ (2 * (a - 1)) * Real.exp (-(y * x ^ 2)))
        = 2 * ((x * x ^ (2 * (a - 1))) * Real.exp (-(y * x ^ 2))) := by ring
      _ = _ := by rw [e4]
  rw [hcongr, integral_const_mul] at hsub
  linarith

private theorem integrableOn_rpow_mul_exp_neg_mul_sq {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t ^ (2 * a - 1) * Real.exp (-(y * t ^ 2))) (Ioi 0) := by
  apply integrable_of_integral_ne_zero
  rw [integral_rpow_mul_exp_neg_mul_sq ha hy]
  exact mul_ne_zero (by norm_num) (mul_ne_zero (by positivity) (Real.Gamma_pos_of_pos ha).ne')

private theorem integrableOn_rpow_mul_one_add_sq_rpow_neg {p σ : ℝ} (hp : -1 < p) (hσ : 0 < σ) (hpσ
  : p - 2 * σ < -1) :
    IntegrableOn (fun t : ℝ => t ^ p * (1 + t ^ 2) ^ (-σ)) (Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ => t ^ p * (1 + t ^ 2) ^ (-σ)) :=
    (measurable_id.pow_const p).mul ((measurable_const.add (measurable_id.pow_const 2)).pow_const _)
  have hnn : ∀ t : ℝ, 0 < t → 0 ≤ t ^ p * (1 + t ^ 2) ^ (-σ) := fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (by positivity) _)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  ·
    have h1 : IntegrableOn (fun t : ℝ => t ^ p) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' hp).1
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht.1)]
    have : (1 + t ^ 2) ^ (-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by linarith)
    calc t ^ p * (1 + t ^ 2) ^ (-σ) ≤ t ^ p * 1 :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ht.1.le _)
      _ = t ^ p := mul_one _
  ·
    have h1 : IntegrableOn (fun t : ℝ => t ^ (p - 2 * σ)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt
      hpσ one_pos
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 1 < t := ht
    have ht0 : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht0)]
    have hle : (1 + t ^ 2) ^ (-σ) ≤ (t ^ 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have e : (t ^ 2) ^ (-σ) = t ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]; push_cast; ring_nf
    calc t ^ p * (1 + t ^ 2) ^ (-σ) ≤ t ^ p * (t ^ 2) ^ (-σ) :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg ht0.le _)
      _ = t ^ (p - 2 * σ) := by rw [e, ← Real.rpow_add ht0]; ring_nf

private theorem integrableOn_rpow_mul_exp_neg_mul_add_inv {c : ℝ} (hc : 0 < c) (n : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (n - 1) * Real.exp (-(c * (t + t⁻¹)))) (Ioi 0) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-n)
  have hnk : 0 < n + k := by linarith
  have hI := (integrableOn_rpow_mul_exp_neg_mul hnk hc).const_mul ((k.factorial : ℝ) / c ^ k)
  have hmeas : Measurable (fun t : ℝ => t ^ (n - 1) * Real.exp (-(c * (t + t⁻¹)))) :=
    (measurable_id.pow_const _).mul (Real.measurable_exp.comp ((measurable_const.mul
      (measurable_id.add measurable_inv)).neg))
  refine hI.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
  have ht : 0 < t := ht
  have hct : 0 < c / t := div_pos hc ht

  have hexp : Real.exp (-(c * t⁻¹)) ≤ (k.factorial : ℝ) / c ^ k * t ^ (k : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (c / t) hct.le k
    have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hpos : 0 < (c / t) ^ k / k.factorial := by positivity
    rw [show -(c * t⁻¹) = -(c / t) by ring, Real.exp_neg]
    calc (Real.exp (c / t))⁻¹ ≤ ((c / t) ^ k / k.factorial)⁻¹ := inv_anti₀ hpos h1
      _ = (k.factorial : ℝ) / c ^ k * t ^ (k : ℝ) := by
          rw [Real.rpow_natCast, div_pow]; field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  have esplit : Real.exp (-(c * (t + t⁻¹))) = Real.exp (-(c * t)) * Real.exp (-(c * t⁻¹)) := by
    rw [← Real.exp_add]; ring_nf
  rw [esplit]
  calc t ^ (n - 1) * (Real.exp (-(c * t)) * Real.exp (-(c * t⁻¹)))
      ≤ t ^ (n - 1) * (Real.exp (-(c * t)) * ((k.factorial : ℝ) / c ^ k * t ^ (k : ℝ))) := by
        gcongr
    _ = (k.factorial : ℝ) / c ^ k * (t ^ (n + k - 1) * Real.exp (-(c * t))) := by
        rw [show n + (k : ℝ) - 1 = (n - 1) + k by ring, Real.rpow_add ht]; ring

private theorem norm_besselIntegrand (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖(Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))‖ =
      t ^ (ν.re - 1) * Real.exp (-(x / 2 * (t + t⁻¹))) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re, mul_comm]
  congr 1; ring_nf

private theorem continuousAt_besselKernel (ν : ℂ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ContinuousAt (fun x : ℝ => besselKernel ν x) x₀ := by
  unfold besselKernel
  have hmeasF : ∀ x : ℝ, Measurable (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ)
    ^ (ν - 1))) :=
    fun x => (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_const.mul (measurable_id.add measurable_inv)).div_const 2).neg))).mul
      ((Complex.measurable_ofReal.comp measurable_id).pow_const _)
  refine continuousAt_of_dominated (bound := fun t : ℝ => t ^ (ν.re - 1) * Real.exp (-(x₀ / 4 * (t
    + t⁻¹))))
    (Filter.Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioi_mem_nhds (show x₀ / 2 < x₀ by linarith)] with x hx
    have hx : x₀ / 2 < x := hx
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 0 < t := ht
    rw [norm_besselIntegrand ν x t ht]
    have hsum : 0 < t + t⁻¹ := by positivity
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith
  · exact integrableOn_rpow_mul_exp_neg_mul_add_inv (by linarith) ν.re
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t _ => ?_)
    exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_id.mul continuous_const).div_const 2).neg)).mul continuous_const).continuousAt

private noncomputable def F (ν s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (s - 1) * (((Real.exp (-(p.1 * (p.2 + p.2⁻¹) / 2)) : ℝ) : ℂ) * ((p.2 : ℂ) ^ (ν - 1)))

private theorem measurable_F (ν s : ℂ) : Measurable (F ν s) := by
  unfold F
  refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    ((Complex.measurable_ofReal.comp (Real.measurable_exp.comp ?_)).mul
      ((Complex.measurable_ofReal.comp measurable_snd).pow_const _))
  exact ((measurable_fst.mul (measurable_snd.add measurable_snd.inv)).div_const 2).neg

private theorem F_eq (ν s : ℂ) (x t : ℝ) :
    F ν s (x, t) = (t : ℂ) ^ (ν - 1) *
      ((x : ℂ) ^ (s - 1) * Complex.exp (-((((t + t⁻¹) / 2 : ℝ) : ℂ) * (x : ℂ)))) := by
  simp only [F, Complex.ofReal_exp]
  push_cast
  ring_nf

private theorem norm_F (ν s : ℂ) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    ‖F ν s (x, t)‖ = t ^ (ν.re - 1) * (x ^ (s.re - 1) * Real.exp (-((t + t⁻¹) / 2 * x))) := by
  rw [F_eq, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp, Complex.sub_re, Complex.one_re, Complex.sub_re, Complex.one_re]
  congr 2
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]

private theorem integrable_F (ν s : ℂ) (hs : |ν.re| < s.re) :
    Integrable (F ν s) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hs
  have hν1 : -s.re < ν.re := by have := neg_abs_le ν.re; linarith
  have hν2 : ν.re < s.re := lt_of_le_of_lt (le_abs_self _) hs
  rw [integrable_prod_iff' (measurable_F ν s).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    have ht : 0 < t := ht
    have hc : 0 < (t + t⁻¹) / 2 := by positivity
    have h1 := (integrableOn_cpow_mul_exp_neg_mul (a := s) hσ hc).const_mul ((t : ℂ) ^ (ν - 1))
    exact IntegrableOn.congr_fun h1 (fun x _ => (F_eq ν s x t).symm) measurableSet_Ioi
  · have hI := (integrableOn_rpow_mul_one_add_sq_rpow_neg (p := ν.re + s.re - 1) (σ := s.re)
      (by linarith) hσ (by linarith)).const_mul ((2 : ℝ) ^ s.re * Real.Gamma s.re)
    refine IntegrableOn.congr_fun hI (fun t ht => ?_) measurableSet_Ioi
    have ht : 0 < t := ht
    have hc : 0 < (t + t⁻¹) / 2 := by positivity
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_F ν s hx ht), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hc]
    have e1 : 1 / ((t + t⁻¹) / 2) = 2 * t * (1 + t ^ 2)⁻¹ := by field_simp; ring
    rw [e1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) ht.le,
      Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    rw [show ν.re + s.re - 1 = (ν.re - 1) + s.re by ring, Real.rpow_add ht]
    ring

private theorem mellin_besselKernel_eq_integral (ν s : ℂ) (hs : |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel ν x) s = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F ν s (x,
        t) := by
  have hF := integrable_F ν s hs
  have hpt : ∀ x : ℝ, (x : ℂ) ^ (s - 1) • besselKernel ν x = ∫ t in Ioi (0 : ℝ), F ν s (x, t) := by
    intro x
    unfold besselKernel
    rw [← integral_smul]
    rfl
  constructor
  · have h1 : Integrable (fun x : ℝ => ∫ t in Ioi (0 : ℝ), F ν s (x, t)) (volume.restrict (Ioi 0))
    :=
      hF.integral_prod_left
    exact h1.congr (Filter.Eventually.of_forall fun x => (hpt x).symm)
  · unfold mellin
    rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) • besselKernel ν x) = fun x => ∫ t in Ioi (0 : ℝ), F ν
      s (x, t) from
      funext hpt]
    exact integral_integral_swap (f := fun x t => F ν s (x, t)) hF

private noncomputable def G (ν s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (ν + s - 1) * ((p.2 : ℂ) ^ (s - 1) * Complex.exp (-((((1 + p.1 ^ 2 : ℝ)) : ℂ) * (p.2
    : ℂ))))

private theorem measurable_G (ν s : ℂ) : Measurable (G ν s) := by
  unfold G
  refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul
    (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul (Measurable.cexp ?_))
  exact ((Complex.measurable_ofReal.comp (measurable_const.add (measurable_fst.pow_const 2))).mul
    (Complex.measurable_ofReal.comp measurable_snd)).neg

private theorem G_eq (ν s : ℂ) (t y : ℝ) :
    G ν s (t, y) = ((y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ))) *
      ((t : ℂ) ^ (2 * ((ν + s) / 2) - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))) := by
  simp only [G]
  have e : Complex.exp (-((((1 + t ^ 2 : ℝ)) : ℂ) * (y : ℂ))) =
      Complex.exp (-(y : ℂ)) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  rw [e, show 2 * ((ν + s) / 2) - 1 = ν + s - 1 by ring]
  ring

private theorem norm_G (ν s : ℂ) {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    ‖G ν s (t, y)‖ = (y ^ (s.re - 1) * Real.exp (-y)) *
      (t ^ (2 * ((ν.re + s.re) / 2) - 1) * Real.exp (-(y * t ^ 2))) := by
  rw [G_eq, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.one_re, Complex.add_re, Complex.div_ofNat_re, zero_mul, sub_zero,
    show ((t : ℂ) ^ 2).re = t ^ 2 by rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _,
    show ((t : ℂ) ^ 2).im = 0 by rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _]
  congr 2
  · congr 1
    simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.add_re, Complex.div_ofNat_im, zero_mul,
      sub_zero]

private theorem integrable_G (ν s : ℂ) (hs : |ν.re| < s.re) :
    Integrable (G ν s) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hs
  have ha : 0 < (ν.re + s.re) / 2 := by have := neg_abs_le ν.re; linarith
  have hb : 0 < (s.re - ν.re) / 2 := by have := le_abs_self ν.re; linarith
  rw [integrable_prod_iff' (measurable_G ν s).aestronglyMeasurable]
  constructor
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    have hy : 0 < y := hy
    have h1 := (integrableOn_rpow_mul_exp_neg_mul_sq ha hy).const_mul (y ^ (s.re - 1) * Real.exp
      (-y))
    refine h1.mono' ((measurable_G ν s).comp (measurable_id.prodMk
      measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => ?_)
    rw [norm_G ν s ht hy]
  · have hI := (integrableOn_rpow_mul_exp_neg_mul hb one_pos).const_mul
      (1 / 2 * Real.Gamma ((ν.re + s.re) / 2))
    refine IntegrableOn.congr_fun hI (fun y hy => ?_) measurableSet_Ioi
    have hy : 0 < y := hy
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => norm_G ν s ht hy), integral_const_mul,
      integral_rpow_mul_exp_neg_mul_sq ha hy, one_div y, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le,
      one_mul]
    have e : y ^ (s.re - 1) * y ^ (-((ν.re + s.re) / 2)) = y ^ ((s.re - ν.re) / 2 - 1) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    rw [← e]
    ring

private theorem integral_G_snd (ν s : ℂ) (hσ : 0 < s.re) {t : ℝ} (ht : 0 < t) :
    ∫ y in Ioi (0 : ℝ), G ν s (t, y) =
      (t : ℂ) ^ (ν + s - 1) * ((1 / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s * Complex.Gamma s) := by
  rw [show (fun y : ℝ => G ν s (t, y)) = fun y : ℝ => (t : ℂ) ^ (ν + s - 1) *
      ((y : ℂ) ^ (s - 1) * Complex.exp (-((((1 + t ^ 2 : ℝ)) : ℂ) * (y : ℂ)))) from rfl,
    integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hσ (by positivity)]

private theorem integral_G_fst (ν s : ℂ) (hs : |ν.re| < s.re) {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), G ν s (t, y) =
      ((y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ))) *
        ((1 / 2 : ℂ) * ((1 / (y : ℂ)) ^ ((ν + s) / 2) * Complex.Gamma ((ν + s) / 2))) := by
  have ha : 0 < ((ν + s) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re]
    have := neg_abs_le ν.re; linarith
  rw [show (fun t : ℝ => G ν s (t, y)) = fun t : ℝ => ((y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ))) *
      ((t : ℂ) ^ (2 * ((ν + s) / 2) - 1) * Complex.exp (-((y : ℂ) * (t : ℂ) ^ 2))) from funext fun
        t => G_eq ν s t y,
    integral_const_mul, integral_cpow_mul_exp_neg_mul_sq ha hy]

private theorem integral_G_swap (ν s : ℂ) (hs : |ν.re| < s.re) :
    ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), G ν s (t, y) = ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      G ν s (t, y) :=
  integral_integral_swap (f := fun t y => G ν s (t, y)) (integrable_G ν s hs)

end MellinK

/-- Mellin transform of the Bessel kernel in terms of Gamma factors. -/
theorem mellin_besselKernel_eq_mul_Gamma_mul_Gamma (ν s : ℂ) (hs : |ν.re| < s.re) :
    MellinConvergent (fun x : ℝ => besselKernel ν x) s ∧
      mellin (fun x : ℝ => besselKernel ν x) s =
        (2 : ℂ) ^ (s - 1) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) := by
  have hσ : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hs
  have ha : 0 < ((ν + s) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re]; have := neg_abs_le ν.re; linarith
  have hb : 0 < ((s - ν) / 2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re]; have := le_abs_self ν.re; linarith
  have h20 : (2 : ℂ) ≠ 0 := two_ne_zero
  obtain ⟨hconv, hmel⟩ := MellinK.mellin_besselKernel_eq_integral ν s hs
  refine ⟨hconv, ?_⟩
  rw [hmel]

  have step1 : ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), MellinK.F ν s (x, t) =
      ∫ t in Ioi (0 : ℝ), (2 : ℂ) ^ s * ∫ y in Ioi (0 : ℝ), MellinK.G ν s (t, y) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht : 0 < t := ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hc : 0 < (t + t⁻¹) / 2 := by positivity
    rw [show (fun x : ℝ => MellinK.F ν s (x, t)) = fun x : ℝ => (t : ℂ) ^ (ν - 1) *
        ((x : ℂ) ^ (s - 1) * Complex.exp (-((((t + t⁻¹) / 2 : ℝ) : ℂ) * (x : ℂ)))) from funext fun
          x => MellinK.F_eq ν s x t,
      integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hσ hc, MellinK.integral_G_snd ν
        s hσ ht]

    have e1 : (1 : ℂ) / ((((t + t⁻¹) / 2 : ℝ)) : ℂ) = (((2 * t : ℝ)) : ℂ) * ((((1 + t ^ 2)⁻¹ : ℝ))
      : ℂ) := by
      have : (1 : ℝ) / ((t + t⁻¹) / 2) = (2 * t) * (1 + t ^ 2)⁻¹ := by field_simp; ring
      rw [← Complex.ofReal_mul, ← this]; push_cast; ring
    have e2 : ((((2 * t : ℝ)) : ℂ) * ((((1 + t ^ 2)⁻¹ : ℝ)) : ℂ)) ^ s =
        (2 : ℂ) ^ s * (t : ℂ) ^ s * ((1 : ℂ) / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s := by
      rw [Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        show (((2 * t : ℝ)) : ℂ) = (((2 : ℝ)) : ℂ) * ((t : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) ht.le]
      push_cast
      ring_nf
    rw [e1, e2]
    have e3 : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ s = (t : ℂ) ^ (ν + s - 1) := by
      rw [← Complex.cpow_add _ _ ht0]; congr 1; ring
    calc (t : ℂ) ^ (ν - 1) * ((2 : ℂ) ^ s * (t : ℂ) ^ s * ((1 : ℂ) / (((1 + t ^ 2 : ℝ)) : ℂ)) ^ s *
      Complex.Gamma s)
        = (2 : ℂ) ^ s * (((t : ℂ) ^ (ν - 1) * (t : ℂ) ^ s) * (((1 : ℂ) / (((1 + t ^ 2 : ℝ)) : ℂ)) ^
          s * Complex.Gamma s)) := by
          ring
      _ = _ := by rw [e3]
  rw [step1, integral_const_mul, MellinK.integral_G_swap ν s hs]

  have step2 : ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), MellinK.G ν s (t, y) =
      ∫ y in Ioi (0 : ℝ), ((1 / 2 : ℂ) * Complex.Gamma ((ν + s) / 2)) *
        ((y : ℂ) ^ ((s - ν) / 2 - 1) * Complex.exp (-((((1 : ℝ)) : ℂ) * (y : ℂ)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy : 0 < y := hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    rw [MellinK.integral_G_fst ν s hs hy]
    have e1 : ((1 : ℂ) / (y : ℂ)) ^ ((ν + s) / 2) = (y : ℂ) ^ (-((ν + s) / 2)) := by
      rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact
        Real.pi_ne_zero.symm),
        Complex.cpow_neg]
    have e2 : (y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-((ν + s) / 2)) = (y : ℂ) ^ ((s - ν) / 2 - 1) := by
      rw [← Complex.cpow_add _ _ hy0]; congr 1; ring
    rw [e1]
    push_cast
    rw [one_mul]
    calc (y : ℂ) ^ (s - 1) * Complex.exp (-(y : ℂ)) * (1 / 2 * ((y : ℂ) ^ (-((ν + s) / 2)) *
      Complex.Gamma ((ν + s) / 2)))
        = 1 / 2 * Complex.Gamma ((ν + s) / 2) * (((y : ℂ) ^ (s - 1) * (y : ℂ) ^ (-((ν + s) / 2))) *
            Complex.exp (-(y : ℂ))) := by ring
      _ = _ := by rw [e2]
  rw [step2, integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hb one_pos]
  push_cast
  rw [div_one, Complex.one_cpow, one_mul, show (ν + s) / 2 = (s + ν) / 2 by ring]
  have e : (2 : ℂ) ^ s * (1 / 2) = (2 : ℂ) ^ (s - 1) := by
    rw [Complex.cpow_sub _ _ h20, Complex.cpow_one]; ring
  calc (2 : ℂ) ^ s * (1 / 2 * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2))
      = ((2 : ℂ) ^ s * (1 / 2)) * Complex.Gamma ((s + ν) / 2) * Complex.Gamma ((s - ν) / 2) := by
        ring
    _ = _ := by rw [e]

/-- The Bessel kernel is not identically zero on the positive axis. -/
theorem exists_besselKernel_ne_zero (ν : ℂ) :
    ∃ x : ℝ, 0 < x ∧ besselKernel ν x ≠ 0 := by
  by_contra h
  push Not at h
  set s : ℂ := ((|ν.re| + 2 : ℝ) : ℂ) with hs_def
  have hsre : s.re = |ν.re| + 2 := by rw [hs_def, Complex.ofReal_re]
  have hs : |ν.re| < s.re := by rw [hsre]; linarith
  obtain ⟨-, hmel⟩ := mellin_besselKernel_eq_mul_Gamma_mul_Gamma ν s hs
  have hzero : mellin (fun x : ℝ => besselKernel ν x) s = 0 := by
    unfold mellin
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    show (t : ℂ) ^ (s - 1) • besselKernel ν t = 0
    rw [h t ht, smul_zero]
  rw [hzero] at hmel
  have habs := abs_nonneg ν.re
  have hle := le_abs_self ν.re
  have hge := neg_abs_le ν.re
  have h1 : (2 : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl two_ne_zero
  have hre1 : 0 < ((s + ν) / 2).re := by
    have : ((s + ν) / 2).re = (s.re + ν.re) / 2 := by simp [Complex.add_re]
    rw [this, hsre]; linarith
  have hre2 : 0 < ((s - ν) / 2).re := by
    have : ((s - ν) / 2).re = (s.re - ν.re) / 2 := by simp [Complex.sub_re]
    rw [this, hsre]; linarith
  exact (mul_ne_zero (mul_ne_zero h1 (Complex.Gamma_ne_zero_of_re_pos hre1))
    (Complex.Gamma_ne_zero_of_re_pos hre2)) hmel.symm

/-- Derivatives of the Bessel kernel and of its derivative. -/
theorem hasDerivAt_besselKernel_and_hasDerivAt_deriv_besselKernel
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => besselKernel ν x) (-besselKernel (ν + 1) x + ν / (x : ℂ) *
      besselKernel ν x) x ∧
      HasDerivAt (deriv fun x : ℝ => besselKernel ν x)
        ((1 + ν ^ 2 / (x : ℂ) ^ 2) * besselKernel ν x - (deriv (fun x : ℝ => besselKernel ν x) x) /
          (x : ℂ)) x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'

  have clause1 : ∀ (μ : ℂ) (y : ℝ), 0 < y →
      HasDerivAt (fun x : ℝ => besselKernel μ x) (-besselKernel (μ + 1) y + μ / (y : ℂ) *
        besselKernel μ y) y := by
    intro μ y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have h1 := hasDerivAt_besselKernel μ y hy
    have h2 := mul_besselKernel_eq_mul_sub μ y hy
    refine h1.congr_deriv ?_
    have h3 : μ / (y : ℂ) * besselKernel μ y = (besselKernel (μ + 1) y - besselKernel (μ - 1) y) /
      2 := by
      rw [div_mul_eq_mul_div, div_eq_iff hy0, h2]; ring
    rw [h3]; ring
  refine ⟨clause1 ν x hx, ?_⟩
  set g : ℝ → ℂ := fun y => -besselKernel (ν + 1) y + ν / (y : ℂ) * besselKernel ν y with hg
  have hev : (deriv fun x : ℝ => besselKernel ν x) =ᶠ[nhds x] g := by
    have hmem : Set.Ioi (0 : ℝ) ∈ nhds x := isOpen_Ioi.mem_nhds hx
    refine Filter.eventually_of_mem hmem fun y hy => ?_
    exact (clause1 ν y hy).deriv
  have hdx : deriv (fun x : ℝ => besselKernel ν x) x = -besselKernel (ν + 1) x + ν / (x : ℂ) *
    besselKernel ν x :=
    (clause1 ν x hx).deriv
  have hA : HasDerivAt (fun y : ℝ => besselKernel (ν + 1) y)
      (-besselKernel (ν + 1 + 1) x + (ν + 1) / (x : ℂ) * besselKernel (ν + 1) x) x := clause1 (ν +
        1) x hx
  have hB : HasDerivAt (fun y : ℝ => besselKernel ν y) (-besselKernel (ν + 1) x + ν / (x : ℂ) *
    besselKernel ν x) x :=
    clause1 ν x hx
  have hinv : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹) (-(((x : ℂ)) ^ 2)⁻¹) x :=
    (hasDerivAt_inv hx0).comp_ofReal
  have h3 : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹ * besselKernel ν y)
      ((-(((x : ℂ)) ^ 2)⁻¹) * besselKernel ν x + ((x : ℂ))⁻¹ * (-besselKernel (ν + 1) x + ν / (x :
        ℂ) * besselKernel ν x)) x :=
    hinv.mul hB
  have h4 := (hA.neg).add (h3.const_mul ν)
  have hg' : HasDerivAt g
      (-(-besselKernel (ν + 1 + 1) x + (ν + 1) / (x : ℂ) * besselKernel (ν + 1) x) +
        ν * ((-(((x : ℂ)) ^ 2)⁻¹) * besselKernel ν x +
          ((x : ℂ))⁻¹ * (-besselKernel (ν + 1) x + ν / (x : ℂ) * besselKernel ν x))) x := by
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [hg, Pi.add_apply, Pi.neg_apply]
    ring

  have h2' := mul_besselKernel_eq_mul_sub (ν + 1) x hx
  rw [show ν + 1 - 1 = ν by ring] at h2'
  have hk2 : besselKernel (ν + 1 + 1) x = besselKernel ν x + 2 * ((ν + 1) / (x : ℂ) * besselKernel
    (ν + 1) x) := by
    have h5 : (ν + 1) / (x : ℂ) * besselKernel (ν + 1) x = (besselKernel (ν + 1 + 1) x -
      besselKernel ν x) / 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff hx0, h2']; ring
    rw [h5]; ring
  refine (hg'.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hdx, hk2]
  field_simp
  ring

end ArchBessel
