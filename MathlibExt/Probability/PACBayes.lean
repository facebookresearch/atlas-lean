/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DonskerVaradhan
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Catoni's PAC-Bayes bound

Let the loss `ℓ θ z` take values in `[0, C]`, let `S = (S₁, …, Sₙ)` be an i.i.d. sample from
`D`, and let `π` be a prior on the parameter space `Θ`. Write `R θ = ∫ ℓ θ z dD` for the risk
and `r_S θ = (1/n) ∑ᵢ ℓ θ Sᵢ` for the empirical risk. For `λ > 0` and `δ > 0` (of interest for
`δ < 1`), with probability at least `1 - δ` over `S`, every probability measure `ρ` on `Θ` satisfies

`∫ R dρ ≤ ∫ r_S dρ + λ C² / (8 n) + (KL(ρ ‖ π) + log (1/δ)) / λ`.

## Proof

* Hoeffding's lemma for each `θ` gives `E_S Real.exp (λ (R θ - r_S θ)) ≤ Real.exp (λ² C² / (8 n))`
  (`integral_pi_exp_le`).
* Integrating in `θ` against `π` and swapping the integrals (Tonelli) gives
  `E_S ∫ Real.exp (λ (R - r_S)) dπ ≤ Real.exp (λ² C² / (8 n))` (`lintegral_pi_lintegral_exp_le`).
* The Donsker–Varadhan inequality `∫ f dρ - log ∫ exp f dπ ≤ KL(ρ ‖ π)` with
  `f = λ (R - r_S)` shows that the bound can only fail when
  `∫ Real.exp (λ (R - r_S)) dπ > Real.exp (λ² C² / (8 n)) / δ`, an event of probability at most `δ`
  by Markov's inequality.

## Source

P. Alquier, "User-friendly introduction to PAC-Bayes bounds", *Foundations and Trends in
Machine Learning* (2024), arXiv:2110.11216, Theorem 2.1, proved through the Donsker–Varadhan
variational formula (Alquier's Lemma 2.2).

## Main results

* `integral_exp_mul_sub_le`: Hoeffding's lemma in the form used here.
* `integral_pi_exp_le`: the exponential moment bound for one parameter `θ`.
* `lintegral_pi_lintegral_exp_le`: the same bound integrated against the prior.
* `catoni_pacBayes`: Catoni's PAC-Bayes bound.
-/

@[expose] public section

open MeasureTheory Set InformationTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.PACBayes

open MathlibExt.InformationTheory.DonskerVaradhan

variable {Θ 𝒵 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝒵]

/-- **Hoeffding's lemma in centred exponential form.** If `g` takes values in `[0, C]` and `D`
is a probability measure, then `∫ Real.exp (t (E g - g)) dD ≤ Real.exp (C² t² / 8)` for every
real `t`. This restates Mathlib's `hasSubgaussianMGF_of_mem_Icc` in the form the PAC-Bayes
argument uses. -/
theorem integral_exp_mul_sub_le (D : Measure 𝒵) [IsProbabilityMeasure D] {g : 𝒵 → ℝ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ z, g z ∈ Icc 0 C) (t : ℝ) :
    ∫ z, Real.exp (t * (∫ z', g z' ∂D - g z)) ∂D ≤ Real.exp (C ^ 2 * t ^ 2 / 8) := by
  have h := hasSubgaussianMGF_of_mem_Icc (μ := D) hg.aemeasurable (ae_of_all _ hgC)
  have h2 := h.mgf_le (-t)
  have e1 : mgf (fun z => g z - ∫ z', g z' ∂D) D (-t) =
      ∫ z, Real.exp (t * (∫ z', g z' ∂D - g z)) ∂D := by
    simp only [mgf]
    congr 1
    ext z
    congr 1
    ring
  have e2 : (((‖C - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) * (-t) ^ 2 / 2 = C ^ 2 * t ^ 2 / 8 := by
    push_cast
    rw [sub_zero, Real.norm_eq_abs, div_pow, sq_abs]
    ring
  rw [← e1, ← e2]
  exact h2

/-- **Exponential moment of the generalisation gap for one parameter.** If `g` takes values in
`[0, C]` and `S` is an i.i.d. sample of size `n > 0` from `D`, then
`E_S Real.exp (λ (E g - (1/n) ∑ᵢ g Sᵢ)) ≤ Real.exp (λ² C² / (8 n))`. -/
theorem integral_pi_exp_le (D : Measure 𝒵) [IsProbabilityMeasure D] {g : 𝒵 → ℝ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ z, g z ∈ Icc 0 C) {n : ℕ} (hn : 0 < n) (lam : ℝ) :
    ∫ S, Real.exp (lam * (∫ z, g z ∂D - (n : ℝ)⁻¹ * ∑ i, g (S i))) ∂(Measure.pi fun _ : Fin n => D)
      ≤ Real.exp (lam ^ 2 * C ^ 2 / (8 * n)) := by
  set E := ∫ z, g z ∂D with hE_def
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have key : ∀ S : Fin n → 𝒵, Real.exp (lam * (E - (n : ℝ)⁻¹ * ∑ i, g (S i))) =
      ∏ i, Real.exp (lam / n * (E - g (S i))) := by
    intro S
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  calc ∫ S, Real.exp (lam * (E - (n : ℝ)⁻¹ * ∑ i, g (S i))) ∂(Measure.pi fun _ : Fin n => D)
      = ∫ S, ∏ i, Real.exp (lam / n * (E - g (S i))) ∂(Measure.pi fun _ : Fin n => D) :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = ∏ i : Fin n, ∫ z, Real.exp (lam / n * (E - g z)) ∂D :=
        integral_fintype_prod_eq_prod (fun _ z => Real.exp (lam / n * (E - g z)))
    _ ≤ ∏ i : Fin n, Real.exp (C ^ 2 * (lam / n) ^ 2 / 8) :=
        Finset.prod_le_prod₀ (fun i _ => integral_nonneg fun z => (Real.exp_pos _).le)
          (fun i _ => integral_exp_mul_sub_le D hg hgC _)
    _ = Real.exp (lam ^ 2 * C ^ 2 / (8 * n)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
        congr 1
        field_simp

/-- **The risk inherits the bounds of the loss.** If `ℓ` takes values in `[0, C]` and `D` is a
probability measure, then `∫ ℓ θ z dD ∈ [0, C]` for every `θ`. -/
theorem risk_mem_Icc (D : Measure 𝒵) [IsProbabilityMeasure D] {ℓ : Θ → 𝒵 → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) {C : ℝ} (hℓC : ∀ θ z, ℓ θ z ∈ Icc 0 C) (θ : Θ) :
    ∫ z, ℓ θ z ∂D ∈ Icc 0 C := by
  have hmeas : Measurable (ℓ θ) := hℓ.comp (measurable_const.prodMk measurable_id)
  have hint : Integrable (ℓ θ) D :=
    (integrable_of_bounded hmeas (C := C) fun z => abs_le.2
      ⟨by linarith [(hℓC θ z).1, (hℓC θ z).2], (hℓC θ z).2⟩).1
  exact ⟨integral_nonneg fun z => (hℓC θ z).1,
    (integral_mono hint (integrable_const C) fun z => (hℓC θ z).2).trans (by simp)⟩

omit [MeasurableSpace Θ] [MeasurableSpace 𝒵] in
/-- **The empirical risk inherits the bounds of the loss.** If `ℓ` takes values in `[0, C]`, then
`(1/n) ∑ᵢ ℓ θ Sᵢ ∈ [0, C]` for every `θ` and every sample `S` of size `n > 0`. -/
theorem empiricalRisk_mem_Icc {ℓ : Θ → 𝒵 → ℝ} {C : ℝ} (hℓC : ∀ θ z, ℓ θ z ∈ Icc 0 C) {n : ℕ}
    (hn : 0 < n) (θ : Θ) (S : Fin n → 𝒵) :
    (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i) ∈ Icc 0 C := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨mul_nonneg (inv_nonneg.2 hn'.le) (Finset.sum_nonneg fun i _ => (hℓC θ _).1), ?_⟩
  calc (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i) ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, C := by
        gcongr with i
        exact (hℓC θ _).2
    _ = C := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- **Bounds on the generalisation gap.** If `ℓ` takes values in `[0, C]`, then for every `θ`
and every sample `S`, the risk and the empirical risk differ by at most `C`. -/
theorem abs_risk_sub_empiricalRisk_le (D : Measure 𝒵) [IsProbabilityMeasure D]
    {ℓ : Θ → 𝒵 → ℝ} (hℓ : Measurable (Function.uncurry ℓ)) {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Icc 0 C) {n : ℕ} (hn : 0 < n) (θ : Θ) (S : Fin n → 𝒵) :
    |∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)| ≤ C := by
  have h1 := risk_mem_Icc D hℓ hℓC θ
  have h2 := empiricalRisk_mem_Icc hℓC hn θ S
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Joint measurability of the exponentiated generalisation gap.** The map
`(S, θ) ↦ Real.exp (λ (R θ - r_S θ))` is measurable. -/
theorem measurable_ofReal_exp_gap (D : Measure 𝒵) [IsProbabilityMeasure D]
    {ℓ : Θ → 𝒵 → ℝ} (hℓ : Measurable (Function.uncurry ℓ)) (n : ℕ) (lam : ℝ) :
    Measurable fun p : (Fin n → 𝒵) × Θ => ENNReal.ofReal (Real.exp (lam *
      (∫ z, ℓ p.2 z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ p.2 (p.1 i)))) := by
  have hR : Measurable fun θ => ∫ z, ℓ θ z ∂D :=
    (hℓ.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hsum : Measurable fun p : (Fin n → 𝒵) × Θ => ∑ i, ℓ p.2 (p.1 i) :=
    Finset.measurable_sum _ fun i _ =>
      hℓ.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  exact ENNReal.measurable_ofReal.comp
    ((measurable_const.mul ((hR.comp measurable_snd).sub (measurable_const.mul hsum))).exp)

/-- **Tonelli step.** If `ℓ` takes values in `[0, C]` and `π` is a probability measure on `Θ`,
then `E_S ∫ Real.exp (λ (R - r_S)) dπ ≤ Real.exp (λ² C² / (8 n))`, where `R θ = ∫ ℓ θ z dD` and
`r_S θ = (1/n) ∑ᵢ ℓ θ Sᵢ`. -/
theorem lintegral_pi_lintegral_exp_le (π : Measure Θ) [IsProbabilityMeasure π]
    (D : Measure 𝒵) [IsProbabilityMeasure D] {ℓ : Θ → 𝒵 → ℝ}
    (hℓ : Measurable (Function.uncurry ℓ)) {C : ℝ} (hℓC : ∀ θ z, ℓ θ z ∈ Icc 0 C) {n : ℕ}
    (hn : 0 < n) (lam : ℝ) :
    ∫⁻ S, ∫⁻ θ, ENNReal.ofReal (Real.exp (lam *
        (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)))) ∂π ∂(Measure.pi fun _ : Fin n => D)
      ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * C ^ 2 / (8 * n))) := by
  rw [lintegral_lintegral_swap (measurable_ofReal_exp_gap D hℓ n lam).aemeasurable]
  calc ∫⁻ θ, ∫⁻ S, ENNReal.ofReal (Real.exp (lam *
          (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)))) ∂(Measure.pi fun _ : Fin n => D) ∂π
      ≤ ∫⁻ _θ, ENNReal.ofReal (Real.exp (lam ^ 2 * C ^ 2 / (8 * n))) ∂π := by
        refine lintegral_mono fun θ => ?_
        have hmeas : Measurable fun S : Fin n → 𝒵 =>
            lam * (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)) :=
          measurable_const.mul (measurable_const.sub (measurable_const.mul
            (Finset.measurable_sum _ fun i _ =>
              hℓ.comp (measurable_const.prodMk (measurable_pi_apply i)))))
        have hbd : ∀ S : Fin n → 𝒵,
            |lam * (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i))| ≤ |lam| * C := fun S => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (abs_risk_sub_empiricalRisk_le D hℓ hℓC hn θ S) (abs_nonneg _)
        rw [← ofReal_integral_eq_lintegral_ofReal
          (integrable_of_bounded (μ := Measure.pi fun _ : Fin n => D) hmeas hbd).2
          (ae_of_all _ fun S => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (integral_pi_exp_le D
          (hℓ.comp (measurable_const.prodMk measurable_id)) (hℓC θ) hn lam)
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * C ^ 2 / (8 * n))) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- **Catoni's PAC-Bayes bound.** Let the loss `ℓ θ z` take values in `[0, C]`, let `S` be an
i.i.d. sample of size `n > 0` from a probability measure `D`, and let `π` be a prior
probability measure on `Θ`. For `λ > 0` and `δ > 0` (the statement is of interest for
`δ < 1`, which is not needed in the proof), the event that some probability
measure `ρ` on `Θ` with `KL(ρ ‖ π) < ∞` violates
`∫ R dρ ≤ ∫ r_S dρ + λ C² / (8 n) + (KL(ρ ‖ π) + log (1/δ)) / λ`
has probability at most `δ`; here `R θ = ∫ ℓ θ z dD` is the risk and
`r_S θ = (1/n) ∑ᵢ ℓ θ Sᵢ` the empirical risk. (For `KL(ρ ‖ π) = ∞` the bound is vacuous.)
The event is bounded through the outer measure, so no measurability of it is needed.

Source: P. Alquier, "User-friendly introduction to PAC-Bayes bounds", *Foundations and Trends
in Machine Learning* (2024), arXiv:2110.11216, Theorem 2.1. It is proved through the
Donsker–Varadhan variational formula (Alquier's Lemma 2.2), in the form
`integral_sub_log_integral_exp_le_toReal_klDiv`. -/
theorem catoni_pacBayes (π : Measure Θ) [IsProbabilityMeasure π] (D : Measure 𝒵)
    [IsProbabilityMeasure D] {ℓ : Θ → 𝒵 → ℝ} (hℓ : Measurable (Function.uncurry ℓ)) {C : ℝ}
    (hℓC : ∀ θ z, ℓ θ z ∈ Icc 0 C) {n : ℕ} (hn : 0 < n) {lam δ : ℝ} (hlam : 0 < lam)
    (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => D)
      {S | ¬ ∀ ρ : Measure Θ, IsProbabilityMeasure ρ → klDiv ρ π ≠ ⊤ →
        ∫ θ, (∫ z, ℓ θ z ∂D) ∂ρ ≤ ∫ θ, ((n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)) ∂ρ
          + lam * C ^ 2 / (8 * n) + ((klDiv ρ π).toReal + Real.log (1 / δ)) / lam}
      ≤ ENNReal.ofReal δ := by
  set b := lam ^ 2 * C ^ 2 / (8 * n) with hb_def
  set G : (Fin n → 𝒵) → ℝ≥0∞ := fun S => ∫⁻ θ, ENNReal.ofReal (Real.exp (lam *
      (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)))) ∂π with hG_def
  have hG : Measurable G := (measurable_ofReal_exp_gap D hℓ n lam).lintegral_prod_right'
  have hGint : ∫⁻ S, G S ∂(Measure.pi fun _ : Fin n => D) ≤ ENNReal.ofReal (Real.exp b) :=
    lintegral_pi_lintegral_exp_le π D hℓ hℓC hn lam
  set ε := ENNReal.ofReal (Real.exp b / δ) with hε_def
  have hε0 : ε ≠ 0 := by
    rw [hε_def]
    exact (ENNReal.ofReal_pos.2 (div_pos (Real.exp_pos b) hδ)).ne'
  have hεtop : ε ≠ ⊤ := by
    rw [hε_def]
    exact ENNReal.ofReal_ne_top
  have hR : Measurable fun θ => ∫ z, ℓ θ z ∂D :=
    (hℓ.stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hsub : {S : Fin n → 𝒵 | ¬ ∀ ρ : Measure Θ, IsProbabilityMeasure ρ → klDiv ρ π ≠ ⊤ →
        ∫ θ, (∫ z, ℓ θ z ∂D) ∂ρ ≤ ∫ θ, ((n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)) ∂ρ
          + lam * C ^ 2 / (8 * n) + ((klDiv ρ π).toReal + Real.log (1 / δ)) / lam} ⊆
      {S | ε ≤ G S} := by
    intro S hS
    simp only [mem_ofPred_eq, not_forall, not_le] at hS
    obtain ⟨ρ, hρ, hKL, hlt⟩ := hS
    have hrm : Measurable fun θ => (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i) :=
      measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        hℓ.comp (measurable_id.prodMk measurable_const))
    have hfm : Measurable fun θ =>
        lam * (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)) :=
      measurable_const.mul (hR.sub hrm)
    have hfb : ∀ θ, |lam * (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i))| ≤ lam * C :=
      fun θ => by
        rw [abs_mul, abs_of_pos hlam]
        exact mul_le_mul_of_nonneg_left (abs_risk_sub_empiricalRisk_le D hℓ hℓC hn θ S)
          hlam.le
    have hDV := integral_sub_log_integral_exp_le_toReal_klDiv (μ := ρ) (ν := π) hKL hfm hfb
    have hint_exp := (integrable_of_bounded (μ := π) hfm hfb).2
    have hRb : ∀ θ, |∫ z, ℓ θ z ∂D| ≤ C := fun θ => by
      have := risk_mem_Icc D hℓ hℓC θ
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have hrb : ∀ θ, |(n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)| ≤ C := fun θ => by
      have := empiricalRisk_mem_Icc hℓC hn θ S
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have hRint := (integrable_of_bounded (μ := ρ) hR hRb).1
    have hrint := (integrable_of_bounded (μ := ρ) hrm hrb).1
    have e : ∫ θ, lam * (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)) ∂ρ =
        lam * (∫ θ, (∫ z, ℓ θ z ∂D) ∂ρ - ∫ θ, ((n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)) ∂ρ) := by
      rw [integral_const_mul, integral_sub hRint hrint]
    have hΦpos := integral_exp_pos (μ := π) hint_exp
    have hlog : b + Real.log (1 / δ) < Real.log (∫ θ, Real.exp (lam *
        (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i))) ∂π) := by
      have h1 := mul_lt_mul_of_pos_left hlt hlam
      rw [mul_add, mul_add, mul_div_cancel₀ _ hlam.ne'] at h1
      have h2 : lam * (lam * C ^ 2 / (8 * n)) = b := by rw [hb_def]; ring
      rw [e, mul_sub] at hDV
      linarith
    have hexp : Real.exp b / δ < ∫ θ, Real.exp (lam *
        (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i))) ∂π := by
      have := (Real.lt_log_iff_exp_lt hΦpos).1 hlog
      rwa [Real.exp_add, Real.exp_log (by positivity), mul_one_div] at this
    change ε ≤ ∫⁻ θ, ENNReal.ofReal (Real.exp (lam *
      (∫ z, ℓ θ z ∂D - (n : ℝ)⁻¹ * ∑ i, ℓ θ (S i)))) ∂π
    rw [← ofReal_integral_eq_lintegral_ofReal hint_exp
      (ae_of_all _ fun θ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hexp.le
  calc (Measure.pi fun _ : Fin n => D) _ ≤ (Measure.pi fun _ : Fin n => D) {S | ε ≤ G S} :=
        measure_mono hsub
    _ ≤ (∫⁻ S, G S ∂(Measure.pi fun _ : Fin n => D)) / ε :=
        meas_ge_le_lintegral_div hG.aemeasurable hε0 hεtop
    _ ≤ ENNReal.ofReal (Real.exp b) / ε := by gcongr
    _ = ENNReal.ofReal δ := by
        rw [hε_def, ← ENNReal.ofReal_div_of_pos (div_pos (Real.exp_pos b) hδ)]
        congr 1
        field_simp

end MathlibExt.Probability.PACBayes
