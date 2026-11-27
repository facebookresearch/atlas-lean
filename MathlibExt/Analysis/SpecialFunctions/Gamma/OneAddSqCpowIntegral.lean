/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean`
and
`P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean`
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

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

open MeasureTheory Set Complex

private theorem scaledGammaIntegral {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
      = ((r : ℝ) : ℂ) ^ (-a) * Complex.Gamma a := by
  have hsub := integral_deriv_smul_comp_Ioi
    (f := fun t : ℝ => r * t) (f' := fun _ : ℝ => r)
    (g := fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) (a := 0)
    (by fun_prop)
    (Filter.tendsto_id.const_mul_atTop hr)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul r).hasDerivWithinAt)
    ?_ ?_ ?_
  · simp only [Function.comp_def, mul_zero] at hsub
    have hΓ : (∫ u in Ioi (0 : ℝ), ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1))
        = Complex.Gamma a := (Complex.Gamma_eq_integral ha).symm
    rw [hΓ] at hsub

    have hpt : ∀ t ∈ Ioi (0 : ℝ),
        (r : ℝ) • (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
          = ((r : ℝ) : ℂ) ^ a *
            (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)) := by
      intro t ht
      rw [real_smul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hr.le (le_of_lt ht)]
      have hrne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
      rw [show ((r : ℝ) : ℂ) ^ (a - 1) = ((r : ℝ) : ℂ) ^ a / ((r : ℝ) : ℂ) ^ (1 : ℂ) from
        Complex.cpow_sub _ _ hrne, Complex.cpow_one]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hsub
    have hrpow : ((r : ℝ) : ℂ) ^ a ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hr.ne'))
    calc ∫ t in Ioi (0 : ℝ), ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
        = (((r : ℝ) : ℂ) ^ a)⁻¹ * (((r : ℝ) : ℂ) ^ a *
            ∫ t in Ioi (0 : ℝ), ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hrpow, one_mul]
      _ = (((r : ℝ) : ℂ) ^ a)⁻¹ * Complex.Gamma a := by rw [hsub]
      _ = ((r : ℝ) : ℂ) ^ (-a) * Complex.Gamma a := by
          rw [Complex.cpow_neg]
  · have himg : (fun t : ℝ => r * t) '' Ioi 0 ⊆ Ioi (0 : ℝ) := by
      rintro u ⟨t, ht, rfl⟩
      exact mul_pos hr ht
    refine ContinuousOn.mono ?_ himg
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).continuousOn.mul
      (ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn)
        (fun u hu => Or.inl (by exact_mod_cast hu)))
  · have hIci : IntegrableOn
        (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact Complex.GammaIntegral_convergent ha
    refine hIci.mono_set ?_
    rintro u ⟨t, ht, rfl⟩
    exact mul_nonneg hr.le ht
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hcomp : IntegrableOn
        (fun t : ℝ => ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
        (Ioi 0) := by
      exact (integrableOn_Ioi_comp_mul_left_iff
        (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) 0 hr).mpr
        (by simpa using Complex.GammaIntegral_convergent ha)
    exact hcomp.smul r

private theorem cpow_neg_eq_gamma_inv_mul_integral {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-a)
      = (Complex.Gamma a)⁻¹ *
        ∫ t in Ioi (0 : ℝ), ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ)
          * ((t : ℝ) : ℂ) ^ (a - 1) := by
  have hx : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [scaledGammaIntegral ha hx, mul_comm (((1 + x ^ 2 : ℝ) : ℂ) ^ (-a)) (Complex.Gamma a),
    ← mul_assoc, inv_mul_cancel₀ (Complex.Gamma_ne_zero_of_re_pos ha), one_mul]

private theorem integrableOn_scaledGamma {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
      (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
      (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ) * ((u : ℝ) : ℂ) ^ (a - 1)) 0 hr).mpr
      (by simpa using Complex.GammaIntegral_convergent ha)
  refine IntegrableOn.congr_fun
    (Integrable.const_mul hbase (((r : ℝ) : ℂ) ^ ((1 : ℂ) - a))) ?_ measurableSet_Ioi
  intro t ht
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  show ((r : ℝ) : ℂ) ^ ((1 : ℂ) - a)
      * (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((r * t : ℝ) : ℂ) ^ (a - 1))
    = ((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
  have hsplit : ((r * t : ℝ) : ℂ) ^ (a - 1)
      = ((r : ℝ) : ℂ) ^ (a - 1) * ((t : ℝ) : ℂ) ^ (a - 1) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (le_of_lt ht)]
  rw [hsplit,
    show ((r : ℝ) : ℂ) ^ ((1 : ℂ) - a)
        * (((Real.exp (-(r * t)) : ℝ) : ℂ)
          * (((r : ℝ) : ℂ) ^ (a - 1) * ((t : ℝ) : ℂ) ^ (a - 1)))
      = ((r : ℝ) : ℂ) ^ ((1 : ℂ) - a) * ((r : ℝ) : ℂ) ^ (a - 1)
        * (((Real.exp (-(r * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)) by ring,
    ← Complex.cpow_add _ _ hrne,
    show ((1 : ℂ) - a) + (a - 1) = 0 by ring, Complex.cpow_zero, one_mul]

private theorem integrable_one_add_sq_rpow_neg {c : ℝ} (hc : 1 / 2 < c) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (-c)) := by
  have hpt : ∀ x : ℝ, (0 : ℝ) < 1 + x ^ 2 := fun x => by positivity

  have htail : ∀ x : ℝ, 1 ≤ |x| → (1 + x ^ 2) ^ (-c) ≤ |x| ^ (-(2 * c)) := by
    intro x hx
    have hx0 : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hx
    have hsq : |x| ^ (2 : ℝ) ≤ 1 + x ^ 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
      linarith [sq_nonneg x]
    calc (1 + x ^ 2) ^ (-c) ≤ (|x| ^ (2 : ℝ)) ^ (-c) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx0 2) hsq (by linarith)
      _ = |x| ^ (-(2 * c)) := by
          rw [← Real.rpow_mul hx0.le]
          ring_nf
  have hcont : Continuous (fun x : ℝ => (1 + x ^ 2) ^ (-c)) :=
    (continuous_const.add (continuous_pow 2)).rpow_const fun x => Or.inl (hpt x).ne'

  have hmid : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-c)) (Icc (-1) 1) :=
    hcont.continuousOn.integrableOn_Icc

  have hright : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-c)) (Ioi 1) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by linarith : -(2*c) < -1)
      one_pos)) (hcont.measurable.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hpt x) _)]
    have h1x : 1 ≤ |x| := by
      rw [le_abs]; left; exact le_of_lt hx
    calc (1 + x ^ 2) ^ (-c) ≤ |x| ^ (-(2 * c)) := htail x h1x
      _ = x ^ (-(2 * c)) := by rw [abs_of_pos (lt_trans one_pos hx)]

  have hleft : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-c)) (Iio (-1)) := by
    have : IntegrableOn (fun x : ℝ => (1 + (-x) ^ 2) ^ (-c)) (Ioi 1) := by
      simpa [neg_sq] using hright
    have hneg := this.comp_neg
    simpa [neg_sq, Set.neg_Ioi] using hneg

  have hunion : IntegrableOn (fun x : ℝ => (1 + x ^ 2) ^ (-c))
      (Iio (-1) ∪ Icc (-1) 1 ∪ Ioi 1) := (hleft.union hmid).union hright
  have hcover : Iio (-1 : ℝ) ∪ Icc (-1) 1 ∪ Ioi 1 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ, iff_true]
    rcases lt_trichotomy x (-1) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨le_of_eq h.symm, by linarith⟩)
    · rcases le_or_gt x 1 with h2 | h2
      · exact Or.inl (Or.inr ⟨le_of_lt h, h2⟩)
      · exact Or.inr h2
  rw [← integrableOn_univ]
  exact hunion.mono_set hcover.symm.subset

private theorem integrable_uncurry_kernel {a : ℂ} (ha : 1 / 2 < a.re) :
    Integrable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
        ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict (Ioi 0))) := by
  have ha0 : 0 < a.re := by linarith
  have hpt : ∀ x : ℝ, (0 : ℝ) < 1 + x ^ 2 := fun x => by positivity
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
      ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ ?_
    · exact Complex.measurable_ofReal.comp
        ((Real.continuous_exp.measurable).comp
          ((((continuous_const.add (continuous_pow 2)).comp continuous_fst).mul
            continuous_snd).neg.measurable))
    · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    have h__af := integrableOn_scaledGamma ha0 (hpt x)
    simp at h__af ⊢
    exact h__af
  · have hnorm : ∀ x : ℝ, (fun t : ℝ => ‖((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ)
        * ((t : ℝ) : ℂ) ^ (a - 1)‖) =ᵐ[MeasureTheory.volume.restrict (Ioi 0)]
        fun t : ℝ => t ^ (a.re - 1) * Real.exp (-((1 + x ^ 2) * t)) := by
      intro x
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp [mul_comm]
    have hval : ∀ x : ℝ, (∫ t in Ioi (0 : ℝ),
        ‖((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)‖)
        = (1 / (1 + x ^ 2)) ^ a.re * Real.Gamma a.re := by
      intro x
      rw [MeasureTheory.integral_congr_ae (hnorm x)]
      have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a.re) (r := 1 + x ^ 2)
        ha0 (hpt x)
      simpa [sub_re, one_re] using this
    refine MeasureTheory.Integrable.congr
      ((integrable_one_add_sq_rpow_neg ha).const_mul (Real.Gamma a.re)) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    show Real.Gamma a.re * (1 + x ^ 2) ^ (-a.re)
      = ∫ t in Ioi (0 : ℝ), ‖((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ)
          * ((t : ℝ) : ℂ) ^ (a - 1)‖
    rw [hval x, one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (hpt x).le,
      neg_one_mul, mul_comm]

private theorem integral_cpow_neg_one_add_sq {a : ℂ} (ha : 1 / 2 < a.re) :
    ∫ x : ℝ, (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-a)
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.Gamma (a - 1 / 2) / Complex.Gamma a := by
  have ha0 : 0 < a.re := by linarith
  have ha12 : 0 < (a - 1 / 2).re := by
    rw [Complex.sub_re]
    norm_num
    linarith
  have hpt : ∀ x : ℝ, (0 : ℝ) < 1 + x ^ 2 := fun x => by positivity
  have hΓne : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0

  have h1 : ∫ x : ℝ, (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-a)
      = (Complex.Gamma a)⁻¹ * ∫ x : ℝ, ∫ t in Ioi (0 : ℝ),
          ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simpa using cpow_neg_eq_gamma_inv_mul_integral ha0 x)

  have h2 : ∫ x : ℝ, ∫ t in Ioi (0 : ℝ),
        ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
      = ∫ t in Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1) :=
    MeasureTheory.integral_integral_swap (integrable_uncurry_kernel ha)

  have h3 : ∀ t ∈ Ioi (0 : ℝ),
      (∫ x : ℝ, ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
        = ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
          * ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ) := by
    intro t ht
    have htC : (0 : ℝ) < t := ht
    have hsplit : ∀ x : ℝ,
        ((Real.exp (-((1 + x ^ 2) * t)) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
          = (((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1))
            * Complex.exp (-((t : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ 2) := by
      intro x
      have hexp : Real.exp (-((1 + x ^ 2) * t)) = Real.exp (-t) * Real.exp (-(t * x ^ 2)) := by
        rw [← Real.exp_add]
        ring_nf
      rw [hexp, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
      MeasureTheory.integral_const_mul, integral_gaussian_complex (by simpa using htC)]

  have h4 : ∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
        * ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.Gamma (a - 1 / 2) := by
    have hptw : ∀ t ∈ Ioi (0 : ℝ),
        ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
          * ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
        = (Real.pi : ℂ) ^ (1 / 2 : ℂ)
          * (((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1 / 2 - 1)) := by
      intro t ht
      have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      have hdiv : ((Real.pi : ℂ) / ((t : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (((t : ℝ) : ℂ) ^ (1 / 2 : ℂ))⁻¹ := by
        rw [div_eq_mul_inv, ← Complex.ofReal_inv,
          Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (inv_nonneg.mpr (le_of_lt ht)),
          Complex.ofReal_inv,
          Complex.inv_cpow _ _ (by
            rw [Complex.arg_ofReal_of_nonneg (le_of_lt ht)]
            exact fun h => Real.pi_ne_zero h.symm)]
      rw [hdiv, ← Complex.cpow_neg]
      rw [show ((Real.exp (-t) : ℝ) : ℂ) * ((t : ℝ) : ℂ) ^ (a - 1)
            * ((Real.pi : ℂ) ^ (1 / 2 : ℂ) * ((t : ℝ) : ℂ) ^ (-(1 / 2) : ℂ))
          = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (((Real.exp (-t) : ℝ) : ℂ)
            * (((t : ℝ) : ℂ) ^ (a - 1) * ((t : ℝ) : ℂ) ^ (-(1 / 2) : ℂ))) by ring,
        ← Complex.cpow_add _ _ htne,
        show (a - 1) + (-(1 / 2) : ℂ) = a - 1 / 2 - 1 by ring]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hptw,
      MeasureTheory.integral_const_mul]
    congr 1
    exact (Complex.Gamma_eq_integral ha12).symm

  rw [h1, h2, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h3, h4]
  field_simp

private theorem arch_integral_value {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, (((1 + x ^ 2 : ℝ)) : ℂ) ^ (-(s + 1 / 2))
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) * Complex.Gamma s / Complex.Gamma (s + 1 / 2) := by
  have ha : 1 / 2 < (s + 1 / 2).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  rw [integral_cpow_neg_one_add_sq ha,
    show (s + 1 / 2 - 1 / 2 : ℂ) = s by ring]

private theorem gammaR_two_mul (s : ℂ) :
    Gammaℝ (2 * s) = (Real.pi : ℂ) ^ (-s) * Complex.Gamma s := by
  rw [Gammaℝ]
  congr 1
  · congr 1; ring
  · congr 1; ring

private theorem gammaR_two_mul_add_one (s : ℂ) :
    Gammaℝ (2 * s + 1) = (Real.pi : ℂ) ^ (-s - 1/2) * Complex.Gamma (s + 1/2) := by
  rw [Gammaℝ]
  congr 1
  · congr 1; ring
  · congr 1; ring

private theorem sqrtpi_gamma_mul_gammaR : ∀ s : ℂ,
    (Real.pi : ℂ) ^ (1/2 : ℂ) * Complex.Gamma s * Gammaℝ (2 * s + 1)
      = Complex.Gamma (s + 1/2) * Gammaℝ (2 * s) := by
  intro s
  rw [gammaR_two_mul, gammaR_two_mul_add_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hfold : (Real.pi : ℂ) ^ (1/2 : ℂ) * (Real.pi : ℂ) ^ (-s - 1/2)
      = (Real.pi : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hπ]
    congr 1
    ring
  calc (Real.pi : ℂ) ^ (1/2 : ℂ) * Complex.Gamma s
        * ((Real.pi : ℂ) ^ (-s - 1/2) * Complex.Gamma (s + 1/2))
      = ((Real.pi : ℂ) ^ (1/2 : ℂ) * (Real.pi : ℂ) ^ (-s - 1/2))
        * (Complex.Gamma s * Complex.Gamma (s + 1/2)) := by ring
    _ = (Real.pi : ℂ) ^ (-s) * (Complex.Gamma s * Complex.Gamma (s + 1/2)) := by
        rw [hfold]
    _ = Complex.Gamma (s + 1/2) * ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) := by ring

private theorem integral_value_gammaR {s : ℂ} (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) := by
  rw [arch_integral_value hs]
  have hΓ : Complex.Gamma (s + 1 / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [Complex.add_re]
    norm_num
    linarith
  have hR : Complex.Gammaℝ (2 * s + 1) ≠ 0 := by
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.mul_re]
    norm_num
    linarith
  rw [div_eq_div_iff hΓ hR, mul_comm (Complex.Gammaℝ (2 * s)) (Complex.Gamma (s + 1 / 2))]
  exact sqrtpi_gamma_mul_gammaR s

/-- The integral of `(1 + x ^ 2) ^ (-(s + 1 / 2))` over `ℝ` is the ratio
`Gammaℝ (2 * s) / Gammaℝ (2 * s + 1)` for `0 < s.re`. -/
public theorem AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = Complex.Gammaℝ (2 * s) / Complex.Gammaℝ (2 * s + 1) :=
  integral_value_gammaR hs
