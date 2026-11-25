/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# The Donsker–Varadhan inequality and the Gibbs variational principle

For probability measures `μ`, `ν` and a bounded measurable function `f`,

`∫ f dμ - log ∫ exp f dν ≤ KL(μ ‖ ν)`.                                  (DV)

This is the inequality half of the Donsker–Varadhan variational formula
`KL(μ ‖ ν) = sup_f [∫ f dμ - log ∫ exp f dν]` (the supremum over bounded measurable `f`), whose
other half is proved in `MathlibExt.InformationTheory.DonskerVaradhanFormula`. Read
the other way round it is the Gibbs variational principle

`log ∫ exp f dν = max_μ [∫ f dμ - KL(μ ‖ ν)]`,

whose maximum is attained at the tilted (Gibbs) measure `dν_f = exp f dν / ∫ exp f dν`. These
are the two Legendre-dual descriptions of relative entropy that Varadhan uses as the starting
point of Sanov's theorem, and they are the "change of measure" inequality behind PAC-Bayes
bounds in learning theory.

The proof is the tilting identity `KL(μ ‖ ν_f) = KL(μ ‖ ν) - ∫ f dμ + log ∫ exp f dν` (Mathlib's
`integral_llr_tilted_right`) together with `KL(μ ‖ ν_f) ≥ 0`.

## Sources

* S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
  Section 3 (Sanov's theorem), Lemma 1.2 in the notes' numbering
  (https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf): the variational formula for relative
  entropy, with bounded measurable test functions.
* S. R. S. Varadhan, "Large deviations", *Ann. Probab.* 36 (2008), 397–419, Section 2
  (arXiv:0804.2330): the dual pair `log ∫ e^V dα = sup_β [∫ V dβ - H(β, α)]` and
  `H(β, α) = sup_V [∫ V dβ - log ∫ e^V dα]`.

## Main results

* `integral_sub_log_integral_exp_le_integral_llr`: (DV) with `∫ llr μ ν dμ` on the right, under
  integrability hypotheses.
* `integral_sub_log_integral_exp_le_toReal_klDiv`: (DV) for bounded measurable `f` when the
  divergence is finite.
* `ofReal_integral_sub_log_integral_exp_le_klDiv`: (DV) for bounded measurable `f`, in `[0, ∞]`,
  with no finiteness hypothesis.
* `toReal_klDiv_tilted`: `KL(ν_f ‖ ν) = ∫ f dν_f - log ∫ exp f dν`.
* `isGreatest_integral_sub_klDiv`: the Gibbs variational principle.
-/

@[expose] public section

open MeasureTheory Real Set InformationTheory
open scoped ENNReal

namespace MathlibExt.InformationTheory.DonskerVaradhan

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ}

/-- **Donsker–Varadhan inequality, integral form.** Let `μ` and `ν` be probability measures with
`μ ≪ ν` and integrable log-likelihood ratio `llr μ ν` under `μ`, and let `f` be `μ`-integrable
with `exp ∘ f` `ν`-integrable. Then
`∫ f dμ - log ∫ exp f dν ≤ ∫ log (dμ/dν) dμ`.
Source: Varadhan, *Large Deviations*, NYU lecture notes, 2010, Section 3, Lemma 1.2 (the
inequality half of the variational formula). -/
theorem integral_sub_log_integral_exp_le_integral_llr [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable f μ) (hfν : Integrable (fun x => exp (f x)) ν) :
    ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) ≤ ∫ x, llr μ ν x ∂μ := by
  have htilt := integral_llr_tilted_right hμν hfμ hfν h_int
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : μ ≪ ν.tilted f := hμν.trans (absolutelyContinuous_tilted hfν)
  have hnonneg : 0 ≤ ∫ x, llr μ (ν.tilted f) x ∂μ := by
    rw [← toReal_klDiv_of_measure_eq hac (by simp)]
    exact ENNReal.toReal_nonneg
  linarith

/-- **Integrability of bounded test functions.** A bounded measurable real function is integrable
for a finite measure, and so is its exponential. -/
lemma integrable_of_bounded [IsFiniteMeasure μ] (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ ∧ Integrable (fun x => exp (f x)) μ := by
  refine ⟨Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x), ?_⟩
  refine Integrable.of_bound (hf.exp).aestronglyMeasurable (exp C)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr ((le_abs_self _).trans (hC x))

/-- **Donsker–Varadhan inequality for bounded test functions.** For probability measures `μ`,
`ν` with `KL(μ ‖ ν) < ∞` and a bounded measurable `f`,
`∫ f dμ - log ∫ exp f dν ≤ KL(μ ‖ ν)`.
Source: Varadhan, *Large Deviations*, NYU lecture notes, 2010, Section 3, Lemma 1.2. -/
theorem integral_sub_log_integral_exp_le_toReal_klDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hKL : klDiv μ ν ≠ ⊤) (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) ≤ (klDiv μ ν).toReal := by
  obtain ⟨hμν, h_int⟩ := klDiv_ne_top_iff.mp hKL
  rw [toReal_klDiv_of_measure_eq hμν (by simp)]
  exact integral_sub_log_integral_exp_le_integral_llr hμν h_int
    (integrable_of_bounded hf hC).1 (integrable_of_bounded hf hC).2

/-- **Donsker–Varadhan inequality in extended nonnegative reals.** For probability measures `μ`,
`ν` and a bounded measurable `f`, `(∫ f dμ - log ∫ exp f dν)⁺ ≤ KL(μ ‖ ν)`, with no finiteness
assumption on the divergence. Taking the supremum over `f` gives one half of the
Donsker–Varadhan variational formula for relative entropy (Varadhan, *Large Deviations*, NYU
lecture notes, 2010, Section 3, Lemma 1.2). -/
theorem ofReal_integral_sub_log_integral_exp_le_klDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) ≤ klDiv μ ν := by
  by_cases hKL : klDiv μ ν = ⊤
  · rw [hKL]; exact le_top
  · rw [← ENNReal.ofReal_toReal hKL]
    exact ENNReal.ofReal_le_ofReal (integral_sub_log_integral_exp_le_toReal_klDiv hKL hf hC)

/-- **Relative entropy of a tilted measure.** For a probability measure `ν` and a bounded
measurable `f`, the Gibbs measure `ν_f = ν.tilted f` (density `exp f / ∫ exp f dν`) satisfies
`KL(ν_f ‖ ν) = ∫ f dν_f - log ∫ exp f dν`; in particular the divergence is finite. -/
theorem toReal_klDiv_tilted [IsProbabilityMeasure ν] (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    klDiv (ν.tilted f) ν ≠ ⊤ ∧
      (klDiv (ν.tilted f) ν).toReal =
        ∫ x, f x ∂(ν.tilted f) - log (∫ x, exp (f x) ∂ν) := by
  have hfν := (integrable_of_bounded (μ := ν) hf hC).2
  have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac : ν.tilted f ≪ ν := tilted_absolutelyContinuous ν f
  -- `llr ν_f ν = f - log Z`, `ν`-a.e., hence `ν_f`-a.e.
  have hllr : llr (ν.tilted f) ν =ᵐ[ν.tilted f] fun x => f x - log (∫ x, exp (f x) ∂ν) := by
    have h1 := llr_tilted_left (μ := ν) (ν := ν) Measure.AbsolutelyContinuous.rfl hfν
      hf.aemeasurable
    have h2 := llr_self ν
    refine hac.ae_le ?_
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2, Pi.zero_apply, add_zero]
  have hfint : Integrable f (ν.tilted f) := (integrable_of_bounded hf hC).1
  have hint : Integrable (llr (ν.tilted f) ν) (ν.tilted f) :=
    (integrable_congr hllr).mpr (hfint.sub (integrable_const _))
  have hne : klDiv (ν.tilted f) ν ≠ ⊤ := klDiv_ne_top hac hint
  refine ⟨hne, ?_⟩
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_congr_ae hllr,
    integral_sub hfint (integrable_const _)]
  simp

/-- **Gibbs variational principle.** For a probability measure `ν` and a bounded measurable `f`,
`log ∫ exp f dν = max { ∫ f dμ - KL(μ ‖ ν) : μ a probability measure with KL(μ ‖ ν) < ∞ }`,
the maximum being attained at the tilted measure `ν.tilted f`. This is the Legendre dual of the
Donsker–Varadhan formula: Varadhan, "Large deviations", *Ann. Probab.* 36 (2008), Section 2,
`log ∫ e^V dα = sup_β [∫ V dβ - H(β, α)]`. -/
theorem isGreatest_integral_sub_klDiv [IsProbabilityMeasure ν] (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    IsGreatest {r : ℝ | ∃ μ : Measure α, IsProbabilityMeasure μ ∧ klDiv μ ν ≠ ⊤ ∧
        r = ∫ x, f x ∂μ - (klDiv μ ν).toReal}
      (log (∫ x, exp (f x) ∂ν)) := by
  have hfν := (integrable_of_bounded (μ := ν) hf hC).2
  refine ⟨⟨ν.tilted f, isProbabilityMeasure_tilted hfν, (toReal_klDiv_tilted hf hC).1, ?_⟩, ?_⟩
  · rw [(toReal_klDiv_tilted hf hC).2]; ring
  · rintro r ⟨μ, hμ, hKL, rfl⟩
    have := integral_sub_log_integral_exp_le_toReal_klDiv hKL hf hC
    linarith

end MathlibExt.InformationTheory.DonskerVaradhan
