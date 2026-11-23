/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
public import MathlibExt.Probability.Statistics.Measurement.Generalizability

/-!
# Generalizability and dependability coefficients

For a crossed person-by-item design with `m` items, the
generalizability coefficient is the variance ratio with the relative
error variance `sigmae2 / m`, and the dependability coefficient uses
the absolute error variance `(sigmaI2 + sigmae2) / m`. The
dependability coefficient lies between zero and the generalizability
coefficient, which is at most one; with positive person and item
components the order is strict, and both coefficients are the
corresponding ratios of the crossed-design error variances. The item
count is required nonzero in the definitions, so no coefficient is
assigned to a zero-item design.

## References

The coefficients are the generalizability coefficient `Eρ²` and the
dependability coefficient `φ` of generalizability theory for a
crossed person-by-item design: with universe-score variance `σ²_P`,
relative error variance `σ²_δ = σ²_e / m`, and absolute error
variance `σ²_Δ = (σ²_I + σ²_e) / m`, they are
`Eρ² = σ²_P / (σ²_P + σ²_δ)` and `φ = σ²_P / (σ²_P + σ²_Δ)`.
See R. L. Brennan, *Generalizability Theory* (Springer, 2001), and
L. J. Cronbach, G. C. Gleser, H. Nanda, and N. Rajaratnam,
*The Dependability of Behavioral Measurements* (Wiley, 1972).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables

/-- The generalizability coefficient `sigmaP2 / (sigmaP2 + sigmae2 / m)` of a crossed
person-by-item design with `m` items: the variance ratio `attenuationFactor` with the relative
error variance `sigmae2 / m` as the error variance. At zero total
variance the literature coefficient is undefined; following the
upstream `attenuationFactor`, this definition uses the totalized
value `0` there, which carries no coefficient meaning. -/
noncomputable def generalizabilityCoefficient (sigmaP2 sigmae2 : ℝ) (m : ℕ) [NeZero m] : ℝ :=
  attenuationFactor sigmaP2 (sigmae2 / m)

/-- The dependability coefficient `sigmaP2 / (sigmaP2 + (sigmaI2 + sigmae2) / m)` of a crossed
person-by-item design with `m` items: the variance ratio `attenuationFactor` with the absolute
error variance `(sigmaI2 + sigmae2) / m` as the error variance. At
zero total variance the literature coefficient is undefined; as with
`generalizabilityCoefficient`, the value is the totalized `0` and
carries no coefficient meaning. -/
noncomputable def dependabilityCoefficient (sigmaP2 sigmaI2 sigmae2 : ℝ) (m : ℕ) [NeZero m] : ℝ :=
  attenuationFactor sigmaP2 ((sigmaI2 + sigmae2) / m)

/-- For nonnegative variance components, `m ≥ 1` items, and positive denominators, the
dependability coefficient lies between `0` and the generalizability coefficient, which is at
most `1`. -/
theorem dependability_le_generalizability {sigmaP2 sigmaI2 sigmae2 : ℝ} {m : ℕ} [NeZero m]
    (hsigmaP2 : 0 ≤ sigmaP2) (hsigmaI2 : 0 ≤ sigmaI2) (hsigmae2 : 0 ≤ sigmae2)
    (hm : 1 ≤ m)
    (hrho_den : 0 < sigmaP2 + sigmae2 / m)
    (hphi_den : 0 < sigmaP2 + (sigmaI2 + sigmae2) / m) :
    0 ≤ dependabilityCoefficient sigmaP2 sigmaI2 sigmae2 m
      ∧ dependabilityCoefficient sigmaP2 sigmaI2 sigmae2 m
        ≤ generalizabilityCoefficient sigmaP2 sigmae2 m
      ∧ generalizabilityCoefficient sigmaP2 sigmae2 m ≤ 1 := by
  haveI : NeZero m := ⟨Nat.ne_of_gt (by omega : 0 < m)⟩
  have hm_pos : (0 : ℝ) < m := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  unfold dependabilityCoefficient generalizabilityCoefficient attenuationFactor
  have hI_div : (0 : ℝ) ≤ sigmaI2 / m := by positivity
  have he_div : (0 : ℝ) ≤ sigmae2 / m := by positivity
  have hIe_div : (0 : ℝ) ≤ (sigmaI2 + sigmae2) / m := by positivity
  have hle_den : sigmaP2 + sigmae2 / (m : ℝ) ≤ sigmaP2 + (sigmaI2 + sigmae2) / (m : ℝ) := by
    have h : sigmae2 / (m : ℝ) ≤ (sigmaI2 + sigmae2) / (m : ℝ) := by
      have h2 : sigmae2 ≤ sigmaI2 + sigmae2 := by linarith
      have := div_le_div_of_nonneg_right h2 (le_of_lt hm_pos)
      simpa using this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact div_nonneg hsigmaP2 (le_of_lt hphi_den)
  · exact div_le_div_of_nonneg_left hsigmaP2 hrho_den hle_den
  · rw [div_le_one hrho_den]
    linarith

/-- With positive person and item variance components, the dependability coefficient is
strictly below the generalizability coefficient. -/
theorem dependability_lt_generalizability {sigmaP2 sigmaI2 sigmae2 : ℝ} {m : ℕ} [NeZero m]
    (hsigmaP2 : 0 < sigmaP2) (hsigmaI2 : 0 < sigmaI2) (hsigmae2 : 0 ≤ sigmae2)
    (hm : 1 ≤ m) :
    dependabilityCoefficient sigmaP2 sigmaI2 sigmae2 m
      < generalizabilityCoefficient sigmaP2 sigmae2 m := by
  haveI : NeZero m := ⟨Nat.ne_of_gt (by omega : 0 < m)⟩
  have hm_pos : (0 : ℝ) < m := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold dependabilityCoefficient generalizabilityCoefficient attenuationFactor
  have he_div : (0 : ℝ) ≤ sigmae2 / m := by positivity
  have hI_div : (0 : ℝ) < sigmaI2 / m := by positivity
  have hlt_den : sigmaP2 + sigmae2 / (m : ℝ) < sigmaP2 + (sigmaI2 + sigmae2) / (m : ℝ) := by
    have h : sigmae2 / (m : ℝ) < (sigmaI2 + sigmae2) / (m : ℝ) := by
      have h2 : sigmae2 < sigmaI2 + sigmae2 := by linarith
      have := div_lt_div_of_pos_right h2 hm_pos
      simpa using this
    linarith
  have hrho_den : (0 : ℝ) < sigmaP2 + sigmae2 / (m : ℝ) := by linarith
  exact div_lt_div_of_pos_left hsigmaP2 hrho_den hlt_den

/-- With zero item variance the two coefficients coincide. -/
theorem dependability_eq_generalizability_of_itemVariance_eq_zero
    (sigmaP2 sigmae2 : ℝ) (m : ℕ) [NeZero m] :
    dependabilityCoefficient sigmaP2 0 sigmae2 m
      = generalizabilityCoefficient sigmaP2 sigmae2 m := by
  simp only [dependabilityCoefficient, generalizabilityCoefficient, attenuationFactor, zero_add]

/-- In the crossed person-by-item model, the dependability and generalizability coefficients
with `m = Fintype.card Item` are the variance ratios of the person effect against the absolute
error `Delta_p` and the relative error `delta_p`. -/
theorem dependability_generalizability_eq_variance_ratio
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Person Item : Type*} [Fintype Item] [Nonempty Item] [DecidableEq Item]
    [NeZero (Fintype.card Item)]
    (grandMean : ℝ)
    (X : Person → Item → Ω → ℝ) (P : Person → Ω → ℝ)
    (I : Item → Ω → ℝ) (e : Person → Item → Ω → ℝ)
    (sigmaP2 sigmaI2 sigmae2 : ℝ) (p : Person)
    (hX : ∀ i, X p i
      = fun ω => grandMean + P p ω + I i ω + e p i ω)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ i, MemLp (e p i) 2 μ)
    (hI_cov : ∀ i j, cov[I i, I j; μ]
      = if i = j then sigmaI2 else 0)
    (he_cov : ∀ i j, cov[e p i, e p j; μ]
      = if i = j then sigmae2 else 0)
    (hIe_cov : ∀ i j, cov[I i, e p j; μ] = 0)
    (hP_var : Var[P p; μ] = sigmaP2) :
    dependabilityCoefficient sigmaP2 sigmaI2 sigmae2 (Fintype.card Item)
        = Var[P p; μ] / (Var[P p; μ] + Var[Delta_p grandMean X P p; μ])
      ∧ generalizabilityCoefficient sigmaP2 sigmae2 (Fintype.card Item)
        = Var[P p; μ] / (Var[P p; μ] + Var[delta_p grandMean X P I p; μ]) := by
  haveI : NeZero (Fintype.card Item) := ⟨Nat.ne_of_gt Fintype.card_pos⟩
  have hm_pos : 0 < (Fintype.card Item : ℝ) := by exact_mod_cast Fintype.card_pos
  have hvar := variance_absolute_relative_errors_selected grandMean X P I e
    sigmaI2 sigmae2 p hX hI_mem he_mem hI_cov he_cov hIe_cov hm_pos
  rw [hP_var, hvar.1, hvar.2]
  exact ⟨rfl, rfl⟩

end MathlibExt.Probability.Statistics.Measurement
