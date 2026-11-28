/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaSpeed
public import Domains.Biology.PopulationGenetics.Coalescent.BetaCoalescent
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Beta-coalescent asymptotic for the Laplace exponent

For the `Beta(2 - α, α)` coalescent with `1 < α < 2`, the Laplace exponent
satisfies
`ψ(q) ∼ q ^ α / (Γ(α) α (α - 1))` as `q → ∞`.
The pushforward form states this for any finite measure on `[0, 1]` whose
image in `ℝ` is Mathlib's `betaMeasure (2 - α) α`; the named form applies it
to Atlas's `BetaCoalescent.betaLambda α`.

## Main results

* `LambdaCoalescent.map_val_betaLambda`: pushing `betaLambda α` to `ℝ` gives
  `betaMeasure (2 - α) α`.
* `LambdaCoalescent.tendsto_psi_div_rpow_of_map_val_eq_betaMeasure`: the
  asymptotic under the pushforward hypothesis.
* `LambdaCoalescent.tendsto_psi_div_rpow_betaLambda`: the asymptotic for
  `betaLambda α`.

## References

* J. Berestycki, N. Berestycki and V. Limic, "The Λ-coalescent speed of
  coming down from infinity", *Annals of Probability* 38 (2010), 207–233,
  eq. (10).
-/

@[expose] public section

open MeasureTheory Set Filter Topology unitInterval Real ProbabilityTheory

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

private theorem betaMeasure_compl_Icc (α : ℝ) : betaMeasure (2 - α) α (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Icc.compl]
  have hz : EqOn (betaPDF (2 - α) α) 0 (Icc (0 : ℝ) 1)ᶜ := fun x hx => by
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact betaPDF_eq_zero_of_nonpos h.le
    · exact betaPDF_eq_zero_of_one_le h.le
  rw [setLIntegral_congr_fun measurableSet_Icc.compl hz]
  simp

/-- Pushing `betaLambda α` back to `ℝ` gives `betaMeasure (2 - α) α` for every real `α`: the
clamp `projIcc` is the identity on `[0, 1]`, which carries the whole measure. Its density
`x^{1-α} (1 - x)^{α-1} / B(2 - α, α)` on `(0, 1)` is read with `1 / 0 = 0` and with negative
values as `0`; it is the `Beta(2 - α, α)` law for `0 < α < 2`. -/
theorem map_val_betaLambda (α : ℝ) :
    (BetaCoalescent.betaLambda α).map ((↑) : I → ℝ) = betaMeasure (2 - α) α := by
  rw [BetaCoalescent.betaLambda,
    Measure.map_map measurable_subtype_coe continuous_projIcc.measurable]
  have hae : ((↑) : I → ℝ) ∘ (projIcc (0 : ℝ) 1 zero_le_one) =ᵐ[betaMeasure (2 - α) α] id := by
    have hmem : ∀ᵐ x ∂(betaMeasure (2 - α) α), x ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]; exact betaMeasure_compl_Icc α
    filter_upwards [hmem] with x hx
    simp [projIcc_of_mem _ hx]
  rw [Measure.map_congr hae, Measure.map_id]

private lemma psiKernel_nonneg_beta (q x : ℝ) : 0 ≤ psiKernel q x := by
  unfold psiKernel
  split_ifs with hx
  · positivity
  · apply div_nonneg _ (sq_nonneg x)
    linarith [add_one_le_exp (-(q * x))]

private lemma psiKernel_le_div {q x : ℝ} (hq : 0 ≤ q) (hx : 0 < x) : psiKernel q x ≤ q / x := by
  rw [psiKernel, ite_eq_right hx.ne', div_le_div_iff₀ (by positivity) hx]
  have h1 : exp (-(q * x)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) hx.le]

private lemma measurable_psiKernel_beta (q : ℝ) : Measurable (psiKernel q) := by
  unfold psiKernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

private lemma psiKernel_eq_integral_beta {q x : ℝ} (hq : 0 ≤ q) (hx : x ≠ 0) :
    ∫ t in Ioc 0 q, (q - t) * exp (-(t * x)) = psiKernel q x := by
  rw [← intervalIntegral.integral_of_le hq, psiKernel, ite_eq_right hx]
  have hderiv : ∀ t ∈ uIcc 0 q, HasDerivAt
      (fun t => exp (-(t * x)) / x ^ 2 - (q - t) * exp (-(t * x)) / x)
      ((q - t) * exp (-(t * x))) t := by
    intro t _
    have hE : HasDerivAt (fun t => exp (-(t * x))) (exp (-(t * x)) * (-x)) t := by
      have := ((hasDerivAt_id' t).mul_const x).neg.exp
      simpa using this
    have h1 := hE.div_const (x ^ 2)
    have h2 := (((hasDerivAt_const t q).sub (hasDerivAt_id' t)).mul hE).div_const x
    convert h1.sub h2 using 1
    simp only [Pi.sub_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t => (q - t) * exp (-(t * x))).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, exp_zero, sub_self, sub_zero]
  field_simp
  ring

private lemma integral_rpow_exp_beta {α t : ℝ} (hα2 : α < 2) (ht : 0 < t) :
    ∫ x in Ioi 0, x ^ (1 - α) * exp (-(t * x)) = Gamma (2 - α) * t ^ (α - 2) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2 - α) (r := t) (by linarith) ht
  rw [show (2 - α - 1 : ℝ) = 1 - α by ring] at h
  rw [h, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub, mul_comm]

private lemma integrableOn_rpow_exp_beta {α t : ℝ} (hα2 : α < 2) (ht : 0 < t) :
    IntegrableOn (fun x => x ^ (1 - α) * exp (-(t * x))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_rpow_exp_beta hα2 ht]
  exact (mul_pos (Gamma_pos_of_pos (by linarith)) (Real.rpow_pos_of_pos ht _)).ne'

private lemma integral_poly_beta {α q : ℝ} (hα1 : 1 < α) (hq : 0 < q) :
    ∫ t in Ioc 0 q, (q - t) * t ^ (α - 2) = q ^ α / (α * (α - 1)) := by
  have h1 : ∫ t in Ioc 0 q, (q - t) * t ^ (α - 2) =
      ∫ t in Ioc 0 q, (q * t ^ (α - 2) - t ^ (α - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have : t ^ (α - 1) = t ^ (α - 2) * t := by
      rw [← Real.rpow_add_one ht.1.ne']; congr 1; ring
    simp only [this]; ring
  rw [h1, ← intervalIntegral.integral_of_le hq.le, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
    integral_rpow (Or.inl (by linarith))]
  · rw [show α - 2 + 1 = α - 1 by ring, show α - 1 + 1 = α by ring,
      Real.zero_rpow (by linarith : (0:ℝ) < α - 1).ne',
      Real.zero_rpow (by linarith : (0:ℝ) < α).ne', Real.rpow_sub_one hq.ne']
    have hα1' : α - 1 ≠ 0 := (by linarith : (0:ℝ) < α - 1).ne'
    have hα0 : α ≠ 0 := (by linarith : (0:ℝ) < α).ne'
    field_simp
    ring
  · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul q
  · exact intervalIntegral.intervalIntegrable_rpow' (by linarith)

private lemma main_integral_beta {α q : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hq : 0 < q) :
    IntegrableOn (fun x => x ^ (1 - α) * psiKernel q x) (Ioi 0) ∧
    ∫ x in Ioi 0, x ^ (1 - α) * psiKernel q x = Gamma (2 - α) / (α * (α - 1)) * q ^ α := by
  set F : ℝ → ℝ → ℝ := fun x t => x ^ (1 - α) * ((q - t) * exp (-(t * x))) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc 0 q))) := by
    have : Measurable (fun p : ℝ × ℝ => p.1 ^ (1 - α) * ((q - p.2) * exp (-(p.2 * p.1)))) := by
      fun_prop
    exact this.aestronglyMeasurable
  have hinner : ∀ t ∈ Ioc 0 q,
      ∫ x in Ioi 0, F x t = (q - t) * (Gamma (2 - α) * t ^ (α - 2)) := by
    intro t ht
    rw [← integral_rpow_exp_beta hα2 ht.1, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hF]; ring
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc 0 q))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      refine ((integrableOn_rpow_exp_beta hα2 ht.1).const_mul (q - t)).congr ?_
      exact ae_of_all _ (fun x => by simp only [Function.uncurry_apply_pair, hF]; ring)
    · have hpoly : IntegrableOn (fun t => (q - t) * (Gamma (2 - α) * t ^ (α - 2))) (Ioc 0 q) := by
        have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := q) (r := α - 2)
          (by linarith)
        have h2 := h.continuousOn_mul (g := fun t => (q - t) * Gamma (2 - α)) (by fun_prop)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hq.le] at h2
        exact h2.congr_fun (fun t _ => by simp only; ring) measurableSet_Ioc
      refine hpoly.congr_fun (fun t ht => ?_) measurableSet_Ioc
      dsimp only
      rw [← hinner t ht]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      simp only [Function.uncurry_apply_pair]
      rw [Real.norm_of_nonneg]
      simp only [hF]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _)
        (mul_nonneg (by linarith [ht.2]) (exp_pos _).le)
  have hpsi : ∀ x ∈ Ioi (0:ℝ), ∫ t in Ioc 0 q, F x t = x ^ (1 - α) * psiKernel q x := by
    intro x hx
    rw [← psiKernel_eq_integral_beta hq.le (ne_of_gt hx), ← integral_const_mul]
  constructor
  · have := hint.integral_prod_left
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    exact hpsi x hx
  · calc ∫ x in Ioi 0, x ^ (1 - α) * psiKernel q x
        = ∫ x in Ioi 0, ∫ t in Ioc 0 q, F x t :=
          setIntegral_congr_fun measurableSet_Ioi (fun x hx => (hpsi x hx).symm)
      _ = ∫ t in Ioc 0 q, ∫ x in Ioi 0, F x t := integral_integral_swap hint
      _ = ∫ t in Ioc 0 q, Gamma (2 - α) * ((q - t) * t ^ (α - 2)) :=
          setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [hinner t ht]; ring)
      _ = Gamma (2 - α) / (α * (α - 1)) * q ^ α := by
          rw [integral_const_mul, integral_poly_beta hα1 hq]; ring

private lemma betaPDFReal_nonneg_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  unfold betaPDFReal
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (one_div_nonneg.mpr (beta_pos ha hb).le)
      (Real.rpow_nonneg h.1.le _)) (Real.rpow_nonneg (by linarith [h.2]) _)
  · exact le_rfl

private lemma psi_eq_betaPDF {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (Λ : Measure I) [IsFiniteMeasure Λ]
    (hΛ : Λ.map ((↑) : I → ℝ) = betaMeasure (2 - α) α) (q : ℝ) :
    psi Λ q = ∫ x in Ioi 0, betaPDFReal (2 - α) α x * psiKernel q x := by
  have hemb : MeasurableEmbedding ((↑) : I → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have h1 : psi Λ q = ∫ y, psiKernel q y ∂(betaMeasure (2 - α) α) := by
    rw [← hΛ, hemb.integral_map]; rfl
  have hmeasPDF : Measurable (betaPDF (2 - α) α) := (measurable_betaPDFReal _ _).ennreal_ofReal
  have h2 : ∫ y, psiKernel q y ∂(betaMeasure (2 - α) α) =
      ∫ x, (betaPDF (2 - α) α x).toReal • psiKernel q x :=
    integral_withDensity_eq_integral_toReal_smul hmeasPDF
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _
  have h3 : ∫ x in Ioi 0, (betaPDF (2 - α) α x).toReal • psiKernel q x =
      ∫ x, (betaPDF (2 - α) α x).toReal • psiKernel q x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    simp only [mem_Ioi, not_lt] at hx
    simp only [betaPDF, smul_eq_mul]
    rw [betaPDFReal, ite_eq_right (fun h => by linarith [h.1]), ENNReal.ofReal_zero,
      ENNReal.toReal_zero, zero_mul]
  rw [h1, h2, ← h3]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  simp only [betaPDF, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (betaPDFReal_nonneg_beta (by linarith) (by linarith) x)]

private lemma beta_err_bound {α q x : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hq : 0 ≤ q) (hx : 0 < x) :
    0 ≤ (x ^ (1 - α) / beta (2 - α) α - betaPDFReal (2 - α) α x) * psiKernel q x ∧
    (x ^ (1 - α) / beta (2 - α) α - betaPDFReal (2 - α) α x) * psiKernel q x ≤
      q / beta (2 - α) α * (if x < 1 then x ^ (1 - α) else x ^ (-α)) := by
  have hB : 0 < beta (2 - α) α := beta_pos (by linarith) (by linarith)
  have hK0 := psiKernel_nonneg_beta q x
  have hK1 := psiKernel_le_div hq hx
  have hxa : 0 < x ^ (1 - α) := Real.rpow_pos_of_pos hx _
  by_cases h1 : x < 1
  · have hpdf : betaPDFReal (2 - α) α x =
        1 / beta (2 - α) α * x ^ (1 - α) * (1 - x) ^ (α - 1) := by
      rw [betaPDFReal, ite_eq_left ⟨hx, h1⟩, show (2 - α - 1 : ℝ) = 1 - α by ring]
    have hw1 : (1 - x) ^ (α - 1) ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by linarith)
    have hw2 : 1 - x ≤ (1 - x) ^ (α - 1) := by
      have := Real.rpow_le_rpow_of_exponent_ge (x := 1 - x) (y := 1) (z := α - 1)
        (by linarith) (by linarith) (by linarith)
      rwa [Real.rpow_one] at this
    have hgap : x ^ (1 - α) / beta (2 - α) α - betaPDFReal (2 - α) α x =
        x ^ (1 - α) * (1 - (1 - x) ^ (α - 1)) / beta (2 - α) α := by
      rw [hpdf]; ring
    rw [hgap, ite_eq_left h1]
    have hnn : 0 ≤ x ^ (1 - α) * (1 - (1 - x) ^ (α - 1)) / beta (2 - α) α :=
      div_nonneg (mul_nonneg hxa.le (by linarith)) hB.le
    refine ⟨mul_nonneg hnn hK0, ?_⟩
    calc x ^ (1 - α) * (1 - (1 - x) ^ (α - 1)) / beta (2 - α) α * psiKernel q x
        ≤ x ^ (1 - α) * x / beta (2 - α) α * (q / x) := by
          apply mul_le_mul _ hK1 hK0 (div_nonneg (mul_nonneg hxa.le hx.le) hB.le)
          apply div_le_div_of_nonneg_right _ hB.le
          exact mul_le_mul_of_nonneg_left (by linarith) hxa.le
      _ = q / beta (2 - α) α * x ^ (1 - α) := by field_simp
  · have hpdf : betaPDFReal (2 - α) α x = 0 := by
      rw [betaPDFReal, ite_eq_right (fun h => h1 h.2)]
    rw [hpdf, sub_zero, ite_eq_right h1]
    have hxx : x ^ (-α) = x ^ (1 - α) / x := by
      rw [← Real.rpow_sub_one hx.ne']; congr 1; ring
    refine ⟨mul_nonneg (div_nonneg hxa.le hB.le) hK0, ?_⟩
    calc x ^ (1 - α) / beta (2 - α) α * psiKernel q x
        ≤ x ^ (1 - α) / beta (2 - α) α * (q / x) :=
          mul_le_mul_of_nonneg_left hK1 (div_nonneg hxa.le hB.le)
      _ = q / beta (2 - α) α * x ^ (-α) := by rw [hxx]; field_simp

private lemma integrableOn_beta_bnd {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    IntegrableOn (fun x : ℝ => if x < 1 then x ^ (1 - α) else x ^ (-α)) (Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ => if x < 1 then x ^ (1 - α) else x ^ (-α)) (Ioo 0 1) := by
    refine IntegrableOn.congr_fun
      ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := 1 - α) zero_lt_one).mpr (by linarith))
      (fun x hx => ?_) measurableSet_Ioo
    simp only [ite_eq_left hx.2]
  have h2 : IntegrableOn (fun x : ℝ => if x < 1 then x ^ (1 - α) else x ^ (-α)) (Ici 1) := by
    refine IntegrableOn.congr_fun (f := fun x : ℝ => x ^ (-α)) ?_ (fun x hx => ?_) measurableSet_Ici
    · exact (integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ => x ^ (-α)) (b := 1)).mpr
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one)
    · simp only [ite_eq_right (not_lt.mpr (mem_Ici.mp hx))]
  have := h1.union h2
  rwa [Ioo_union_Ici_eq_Ioi zero_lt_one] at this

private lemma beta_key_bounds {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (Λ : Measure I)
    [IsFiniteMeasure Λ] (hΛ : Λ.map ((↑) : I → ℝ) = betaMeasure (2 - α) α) {q : ℝ} (hq : 0 < q) :
    0 ≤ Gamma (2 - α) / (α * (α - 1)) * q ^ α / beta (2 - α) α - psi Λ q ∧
    Gamma (2 - α) / (α * (α - 1)) * q ^ α / beta (2 - α) α - psi Λ q ≤
      q / beta (2 - α) α * ∫ x in Ioi 0, (if x < 1 then x ^ (1 - α) else x ^ (-α)) := by
  obtain ⟨hint, hval⟩ := main_integral_beta hα1 hα2 hq
  rw [psi_eq_betaPDF hα1 hα2 Λ hΛ q]
  have hint1 := hint.div_const (beta (2 - α) α)
  have hint2 : IntegrableOn (fun x => betaPDFReal (2 - α) α x * psiKernel q x) (Ioi 0) := by
    refine Integrable.mono' hint1 ?_ ?_
    · exact ((measurable_betaPDFReal _ _).mul (measurable_psiKernel_beta q)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h := (beta_err_bound hα1 hα2 hq.le hx).1
      rw [Real.norm_of_nonneg (mul_nonneg (betaPDFReal_nonneg_beta (by linarith) (by linarith) x)
        (psiKernel_nonneg_beta q x))]
      have e : x ^ (1 - α) * psiKernel q x / beta (2 - α) α =
          (x ^ (1 - α) / beta (2 - α) α - betaPDFReal (2 - α) α x) * psiKernel q x +
            betaPDFReal (2 - α) α x * psiKernel q x := by ring
      rw [e]; linarith
  have h_sub := integral_sub hint1 hint2
  rw [integral_div, hval] at h_sub
  have hE : ∫ x in Ioi 0, (x ^ (1 - α) / beta (2 - α) α - betaPDFReal (2 - α) α x) *
      psiKernel q x = Gamma (2 - α) / (α * (α - 1)) * q ^ α / beta (2 - α) α -
        ∫ x in Ioi 0, betaPDFReal (2 - α) α x * psiKernel q x := by
    rw [← h_sub]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  rw [← hE]
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi (fun x hx => (beta_err_bound hα1 hα2 hq.le hx).1)
  · rw [← integral_const_mul]
    refine setIntegral_mono_on ?_ ((integrableOn_beta_bnd hα1 hα2).const_mul _) measurableSet_Ioi
      (fun x hx => (beta_err_bound hα1 hα2 hq.le hx).2)
    exact IntegrableOn.congr_fun (hint1.sub hint2)
      (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi

/-- For a finite measure `Λ` on `[0, 1]` with pushforward `Beta(2 - α, α)`, `1 < α < 2`,
`ψ(q) ∼ q^α / (Γ(α) α (α - 1))` as `q → ∞`. -/
theorem tendsto_psi_div_rpow_of_map_val_eq_betaMeasure {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (Λ : Measure I) [IsFiniteMeasure Λ]
    (hΛ : Λ.map ((↑) : I → ℝ) = betaMeasure (2 - α) α) :
    Tendsto (fun q => psi Λ q / q ^ α) atTop
      (𝓝 (Gamma α * α * (α - 1))⁻¹) := by
  have hB : 0 < beta (2 - α) α := beta_pos (by linarith) (by linarith)
  have hG : 0 < Gamma (2 - α) := Gamma_pos_of_pos (by linarith)
  have hGα : 0 < Gamma α := Gamma_pos_of_pos (by linarith)
  have hL : (Gamma α * α * (α - 1))⁻¹ =
      Gamma (2 - α) / (α * (α - 1)) / beta (2 - α) α := by
    rw [beta, show 2 - α + α = 2 by ring, Gamma_two]
    have hα1' : α - 1 ≠ 0 := (by linarith : (0:ℝ) < α - 1).ne'
    have hα0 : α ≠ 0 := (by linarith : (0:ℝ) < α).ne'
    field_simp
  rw [hL]
  set M := ∫ x in Ioi (0:ℝ), (if x < 1 then x ^ (1 - α) else x ^ (-α)) with hM
  have hlim : Tendsto (fun q : ℝ => Gamma (2 - α) / (α * (α - 1)) / beta (2 - α) α -
      M / beta (2 - α) α * q ^ (1 - α)) atTop
      (𝓝 (Gamma (2 - α) / (α * (α - 1)) / beta (2 - α) α)) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < α - 1)).const_mul
      (M / beta (2 - α) α)).const_sub (Gamma (2 - α) / (α * (α - 1)) / beta (2 - α) α)
    rw [mul_zero, sub_zero, neg_sub] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with q hq
    obtain ⟨_, h2⟩ := beta_key_bounds hα1 hα2 Λ hΛ hq
    rw [← hM] at h2
    have hqa : 0 < q ^ α := Real.rpow_pos_of_pos hq α
    have hq1 : q ^ (1 - α) = q / q ^ α := by rw [Real.rpow_sub hq, Real.rpow_one]
    rw [hq1, le_div_iff₀ hqa]
    have e : (Gamma (2 - α) / (α * (α - 1)) / beta (2 - α) α -
        M / beta (2 - α) α * (q / q ^ α)) * q ^ α =
        Gamma (2 - α) / (α * (α - 1)) * q ^ α / beta (2 - α) α - q / beta (2 - α) α * M := by
      field_simp
    rw [e]; linarith
  · filter_upwards [eventually_gt_atTop 0] with q hq
    obtain ⟨h1, _⟩ := beta_key_bounds hα1 hα2 Λ hΛ hq
    have hqa : 0 < q ^ α := Real.rpow_pos_of_pos hq α
    rw [div_le_iff₀ hqa]
    have e : Gamma (2 - α) / (α * (α - 1)) / beta (2 - α) α * q ^ α =
        Gamma (2 - α) / (α * (α - 1)) * q ^ α / beta (2 - α) α := by ring
    rw [e]; linarith

/-- **Beta-coalescent asymptotic** (Berestycki–Berestycki–Limic, eq. (10)): for
`1 < α < 2`, `ψ(q) / q ^ α → (Γ(α) α (α - 1))⁻¹` for `BetaCoalescent.betaLambda α`. The
finiteness instance always holds, as `betaLambda α` is a probability measure for `0 < α < 2`. -/
theorem tendsto_psi_div_rpow_betaLambda {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    [IsFiniteMeasure (BetaCoalescent.betaLambda α)] :
    Tendsto (fun q => psi (BetaCoalescent.betaLambda α) q / q ^ α) atTop
      (𝓝 (Gamma α * α * (α - 1))⁻¹) :=
  tendsto_psi_div_rpow_of_map_val_eq_betaMeasure hα1 hα2 _ (map_val_betaLambda α)

end MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
