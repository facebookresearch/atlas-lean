/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.InformationInequalityIdentification

/-!
# Tests for identifiability of the population criterion via the information inequality

All models are Bernoulli laws on `Bool` given by densities with respect to the counting measure,
`bernDens q true = q`, `bernDens q false = 1 - q`, observed through `X i = id` on `Ω = Bool`
under the true law `P = densityModel count _ θ₀`. The population criterion is computed from the
definitions (`popCrit_bern`), not through the theorems under test.

* **Non-vacuity.** For the Bernoulli family `θ ↦ Ber(θ)` on `K = [1/4, 3/4]` with `θ₀ = 1/2`,
  every hypothesis of `isIdentifiedOn_popCrit_of_densityModel_of_ae_eq` is discharged and the
  theorem gives `IsIdentifiedOn`. Independently, the computed criterion
  `popCrit θ = (log θ + log (1 - θ)) / 2` satisfies `popCrit (1/4) < popCrit (1/2)`.
* **Identifiability of the law is needed.** For `θ ↦ Ber((1 + θ²) / 4)` on `K = [-1, 1]` with
  `θ₀ = 1/2`, probability, measurability, positivity and integrability hold, the laws at `±1/2`
  coincide, and `IsIdentifiedOn` fails: the criterion takes the same value at `±1/2`.
* **Positivity of the density is needed.** For `θ ↦ Ber(θ)` on `K = [1/2, 1]` with
  `θ₀ = 1/2`, the law is identified, but the density at `θ = 1` vanishes at `false`, where the
  real log-likelihood is `log 0 = 0`; the computed criterion is `0` at `θ = 1` and
  `log (1/2) < 0` at `θ₀`, so `IsIdentifiedOn` fails.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExtTest.Probability.Statistics.InformationInequalityIdentification

open MathlibExt.Probability.Statistics.MLEConsistency
open MathlibExt.Probability.Statistics.InformationInequalityIdentification

/-! ## The Bernoulli density on `Bool` -/

/-- The Bernoulli density with success probability `q` with respect to the counting measure on
`Bool`. -/
noncomputable def bernDens (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- The Bernoulli law `count.withDensity (ofReal ∘ bernDens q)`. -/
noncomputable def bernLaw (q : ℝ) : Measure Bool :=
  Measure.count.withDensity fun b => ENNReal.ofReal (bernDens q b)

@[simp] theorem bernDens_true (q : ℝ) : bernDens q true = q := rfl

@[simp] theorem bernDens_false (q : ℝ) : bernDens q false = 1 - q := rfl

theorem bernDens_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) : 0 ≤ bernDens q b := by
  cases b <;> simp [bernDens] <;> linarith

theorem bernDens_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (b : Bool) : 0 < bernDens q b := by
  cases b <;> simp [bernDens] <;> linarith

/-- For `q ∈ [0, 1]` the Bernoulli law is a probability measure. -/
theorem isProbabilityMeasure_bernLaw {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (bernLaw q) := by
  constructor
  rw [bernLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
    tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun b _ => bernDens_nonneg hq0 hq1 b]
  simp [bernDens]

/-- Integrals against the Bernoulli law, computed from the definitions. -/
theorem integral_bernLaw {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g : Bool → ℝ) :
    ∫ b, g b ∂bernLaw q = q * g true + (1 - q) * g false := by
  rw [bernLaw, integral_withDensity_eq_integral_toReal_smul (measurable_of_countable _)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), integral_count, Fintype.sum_bool]
  simp [bernDens, ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (sub_nonneg.2 hq1)]

/-- The observation: the identity on `Bool`, at every index. -/
def X : ℕ → Bool → Bool := fun _ b => b

/-- The population criterion of a Bernoulli family `θ ↦ Ber(g θ)` under the true law `Ber(q₀)`,
computed from the definitions: `q₀ log (g θ) + (1 - q₀) log (1 - g θ)`. -/
theorem popCrit_bern {Θ : Type*} (g : Θ → ℝ) {q₀ : ℝ} (hq0 : 0 ≤ q₀) (hq1 : q₀ ≤ 1) (θ : Θ) :
    popCrit (bernLaw q₀) (logDensity fun θ => bernDens (g θ)) X θ
      = q₀ * Real.log (g θ) + (1 - q₀) * Real.log (1 - g θ) := by
  rw [popCrit]
  exact (integral_bernLaw hq0 hq1 _).trans (by simp [X, logDensity, bernDens])

/-! ## Non-vacuity: the Bernoulli family on `[1/4, 3/4]` -/

/-- The Bernoulli family `θ ↦ bernDens θ`. -/
noncomputable def bernFam (θ : ℝ) : Bool → ℝ := bernDens θ

theorem densityModel_bernFam (θ : ℝ) :
    densityModel Measure.count bernFam θ = bernLaw θ := rfl

/-- The true law `Ber(1/2)` is a probability measure. -/
instance : IsProbabilityMeasure (densityModel Measure.count bernFam (1 / 2)) :=
  isProbabilityMeasure_bernLaw (by norm_num) (by norm_num)

/-- **Non-vacuity**: every hypothesis of `isIdentifiedOn_popCrit_of_densityModel_of_ae_eq` holds
for the Bernoulli family on `[1/4, 3/4]` at `θ₀ = 1/2`. -/
theorem isIdentifiedOn_bernFam :
    IsIdentifiedOn (Icc (1 / 4 : ℝ) (3 / 4))
      (popCrit (densityModel Measure.count bernFam (1 / 2)) (logDensity bernFam) X) (1 / 2) :=
  isIdentifiedOn_popCrit_of_densityModel_of_ae_eq (by norm_num [mem_Icc])
    (fun θ hθ => isProbabilityMeasure_bernLaw (by linarith [hθ.1]) (by linarith [hθ.2]))
    (fun θ _ => measurable_of_countable _)
    (fun θ hθ => ae_of_all _ fun b =>
      bernDens_pos (q := θ) (by linarith [hθ.1]) (by linarith [hθ.2]) b)
    measurable_id.aemeasurable Measure.map_id (fun θ _ => Integrable.of_finite)
    (fun θ _ h => by simpa [bernFam, bernDens] using Measure.ae_count_iff.1 h true)

/-- The criterion of the Bernoulli family under `Ber(1/2)`, from the definitions. -/
theorem popCrit_bernFam (θ : ℝ) :
    popCrit (densityModel Measure.count bernFam (1 / 2)) (logDensity bernFam) X θ
      = 1 / 2 * Real.log θ + 1 / 2 * Real.log (1 - θ) := by
  rw [densityModel_bernFam, show bernFam = fun θ => bernDens (id θ) from rfl,
    popCrit_bern id (by norm_num) (by norm_num)]
  norm_num

/-- Independent check of the conclusion at `θ = 1/4`, computed from the definitions:
`(log (1/4) + log (3/4)) / 2 < log (1/2)`. -/
example :
    popCrit (densityModel Measure.count bernFam (1 / 2)) (logDensity bernFam) X (1 / 4)
      < popCrit (densityModel Measure.count bernFam (1 / 2)) (logDensity bernFam) X (1 / 2) := by
  rw [popCrit_bernFam, popCrit_bernFam, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have h : Real.log (1 / 4) + Real.log (3 / 4) < Real.log (1 / 2) + Real.log (1 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## Boundary: identifiability of the law is needed -/

/-- A non-injective reparametrization: `θ ↦ Ber((1 + θ²) / 4)`. -/
noncomputable def evenFam (θ : ℝ) : Bool → ℝ := bernDens ((1 + θ ^ 2) / 4)

/-- On `[-1, 1]`, every hypothesis except identifiability of the law holds: probability,
measurability, positivity, and (on a finite space) integrability. -/
theorem evenFam_hypotheses :
    (∀ θ ∈ Icc (-1 : ℝ) 1, IsProbabilityMeasure (densityModel Measure.count evenFam θ)) ∧
    (∀ θ ∈ Icc (-1 : ℝ) 1, Measurable (evenFam θ)) ∧
    (∀ θ ∈ Icc (-1 : ℝ) 1, ∀ᵐ b ∂Measure.count, 0 < evenFam θ b) ∧
    (∀ θ ∈ Icc (-1 : ℝ) 1,
      Integrable (logDensity evenFam θ) (densityModel Measure.count evenFam (1 / 2))) := by
  have hb : ∀ θ ∈ Icc (-1 : ℝ) 1, 0 < (1 + θ ^ 2) / 4 ∧ (1 + θ ^ 2) / 4 < 1 := fun θ hθ => by
    have : θ ^ 2 ≤ 1 := by nlinarith [hθ.1, hθ.2]
    constructor <;> nlinarith [sq_nonneg θ]
  have : IsProbabilityMeasure (densityModel Measure.count evenFam (1 / 2)) :=
    isProbabilityMeasure_bernLaw (by norm_num) (by norm_num)
  refine ⟨fun θ hθ => isProbabilityMeasure_bernLaw (hb θ hθ).1.le (hb θ hθ).2.le,
    fun θ _ => measurable_of_countable _,
    fun θ hθ => ae_of_all _ fun b => bernDens_pos (hb θ hθ).1 (hb θ hθ).2 b,
    fun θ _ => Integrable.of_finite⟩

/-- The laws at `-1/2` and `1/2` coincide. -/
theorem densityModel_evenFam_neg :
    densityModel Measure.count evenFam (-1 / 2) = densityModel Measure.count evenFam (1 / 2) := by
  simp only [densityModel, evenFam]
  norm_num

/-- **Boundary**: without identifiability of the law, `IsIdentifiedOn` fails. -/
theorem not_isIdentifiedOn_evenFam :
    ¬ IsIdentifiedOn (Icc (-1 : ℝ) 1)
      (popCrit (densityModel Measure.count evenFam (1 / 2)) (logDensity evenFam) X) (1 / 2) := by
  intro h
  have hlt := h.2 (-1 / 2) (by norm_num [mem_Icc]) (by norm_num)
  have heq : logDensity evenFam (-1 / 2) = logDensity evenFam (1 / 2) := by
    funext b
    simp only [logDensity, evenFam]
    norm_num
  simp only [popCrit, heq] at hlt
  exact lt_irrefl _ hlt

/-! ## Boundary: positivity of the density is needed -/

/-- The density at `θ = 1` vanishes at `false`, so positivity fails at `θ = 1 ∈ [1/2, 1]`. -/
theorem not_ae_pos_bernFam_one : ¬ ∀ᵐ b ∂Measure.count, 0 < bernFam 1 b := fun h => by
  simpa [bernFam, bernDens] using Measure.ae_count_iff.1 h false

/-- The law of the Bernoulli family is identified on `[1/2, 1]`. -/
theorem bernFam_law_identified :
    ∀ θ ∈ Icc (1 / 2 : ℝ) 1,
      densityModel Measure.count bernFam θ = densityModel Measure.count bernFam (1 / 2) →
        θ = 1 / 2 := by
  intro θ hθ h
  have h1 := (withDensity_eq_iff_of_sigmaFinite (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable).1 h
  have h2 := Measure.ae_count_iff.1 h1 true
  simp only [bernFam, bernDens_true] at h2
  exact (ENNReal.ofReal_eq_ofReal_iff (by linarith [hθ.1]) (by norm_num)).1 h2

/-- **Boundary**: with the law identified but the density vanishing at `θ = 1`, the computed
criterion is `0` at `θ = 1` and `log (1/2) < 0` at `θ₀ = 1/2`, so `IsIdentifiedOn` fails. -/
theorem not_isIdentifiedOn_bernFam_of_not_pos :
    ¬ IsIdentifiedOn (Icc (1 / 2 : ℝ) 1)
      (popCrit (densityModel Measure.count bernFam (1 / 2)) (logDensity bernFam) X) (1 / 2) := by
  intro h
  have hlt := h.2 1 (by norm_num [mem_Icc]) (by norm_num)
  rw [popCrit_bernFam, popCrit_bernFam, sub_self, Real.log_one, Real.log_zero,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hlt
  have hneg := Real.log_neg (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  linarith

end MathlibExtTest.Probability.Statistics.InformationInequalityIdentification
