/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.DoubleMLRates
public import MathlibExtTest.Probability.Causality.AugmentedIPW.CrossFitting

/-!
# Tests for the double-ML rate conditions

* A fair-coin fixture with outcome noise `Y₀ = Y₁ = ±1`, correct outcome regressions and the
  wrong propensity `1/4`. Computed from the definitions, the score error is `20/9` while the
  outcome-regression errors are `0`, so the conditional-variance term of
  `integral_sq_aipwScoreOfSigma_sub_le` is the only term that can cover it; the theorem applies
  with `C = 1`, the conditional variance computed from its definition.
* The correct-nuisance boundary: the bound applies at the true nuisances, where all its error
  terms vanish, and forces the score error to `0`.
* Non-vacuity of `tendstoInDistribution_crossFit_aipw_of_quarter_rates` (and through it of
  `tendstoInDistribution_crossFit_aipw_of_rates`) on i.i.d. Bernoulli(1/2) treatment, with a
  fitted propensity `1/2 + 1/(4(n+1))` and a fitted treated-arm regression `1/(n+1)` that are
  both wrong at every sample size.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting
open MathlibExt.Probability.Causality.AugmentedIPW.DoubleMLRates
open MathlibExtTest.Probability.Causality.AugmentedIPW.CrossFitting

namespace MathlibExtTest.Probability.Causality.AugmentedIPW.DoubleMLRates

/-- Integrals against the fair coin `bern` of the cross-fitting tests. -/
lemma integral_bern (f : Bool → ℝ) : ∫ w, f w ∂bern = (f true + f false) / 2 := by
  rw [integral_fintype (Integrable.of_finite (μ := bern) (f := f))]
  simp [bern, measureReal_def]
  ring

/-- The `±1` outcome. -/
def pmOne (w : Bool) : ℝ := if w then 1 else -1

/-- With trivial covariates the regression of `pmOne` is `0`. -/
lemma bern_pmOne : bern[pmOne | ⊥] = fun _ => (0 : ℝ) := by
  rw [condExp_bot]; funext _
  rw [integral_bern]; simp [pmOne]

/-- The conditional variance of `pmOne` given the trivial σ-algebra is `1`. -/
lemma bern_pmOne_var :
    (bern[fun w => (pmOne w - bern[pmOne | ⊥] w) ^ 2 | ⊥] : Bool → ℝ) = fun _ => (1 : ℝ) := by
  rw [bern_pmOne, condExp_bot]; funext _
  rw [integral_bern]; simp [pmOne]

/-- The observed outcome is `pmOne` when both potential outcomes are `pmOne`. -/
lemma pmOne_observed : ∀ w, pmOne w = observed {true} pmOne pmOne w := fun w => by
  cases w <;> simp [observed, pmOne]

/-- The score error of the fixture computed from the definitions: wrong propensity `1/4`,
correct regressions `0`, true propensity `1/2`. At `true` the scores are `4` and `2`, at `false`
`4/3` and `2`, so the mean squared error is `(4 + 4/9) / 2 = 20/9`. -/
lemma fixture_score_error :
    ∫ w, (aipwScoreOfSigma {true} pmOne (fun _ => 1 / 4) (fun _ => 0) (fun _ => 0) w -
      aipwScoreOfSigma {true} pmOne bern[({true} : Set Bool).indicator 1 | ⊥] bern[pmOne | ⊥]
        bern[pmOne | ⊥] w) ^ 2 ∂bern = 20 / 9 := by
  rw [bern_propensity, bern_pmOne, integral_bern]
  simp [aipwScoreOfSigma_apply, pmOne]
  norm_num

/-- The outcome-regression errors of the fixture vanish and its propensity error is `1/16`, all
computed from the definitions. With the score error `20/9 > 0`, no bound by the
outcome-regression errors alone holds; the propensity term `8 C (ε⁻¹ ε₀⁻¹)² ‖e* - e‖₂²` is needed,
and with `C = 0` it would vanish too. -/
example : ∫ w, (bern[pmOne | ⊥] w - (0 : ℝ)) ^ 2 ∂bern = 0 ∧
    ∫ w, (bern[({true} : Set Bool).indicator (1 : Bool → ℝ) | ⊥] w - (1 / 4 : ℝ)) ^ 2 ∂bern =
      1 / 16 ∧
    0 < ∫ w, (aipwScoreOfSigma {true} pmOne (fun _ => 1 / 4) (fun _ => 0) (fun _ => 0) w -
      aipwScoreOfSigma {true} pmOne bern[({true} : Set Bool).indicator 1 | ⊥] bern[pmOne | ⊥]
        bern[pmOne | ⊥] w) ^ 2 ∂bern := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bern_pmOne]; simp
  · rw [bern_propensity, integral_bern]; norm_num
  · rw [fixture_score_error]; norm_num

/-- `integral_sq_aipwScoreOfSigma_sub_le` applies to the fixture with `ε = 1/4`, `ε₀ = 1/2` and
the conditional variance bound `C = 1` of `bern_pmOne_var`. -/
example : ∫ w, (aipwScoreOfSigma {true} pmOne (fun _ => 1 / 4) (fun _ => 0) (fun _ => 0) w -
      aipwScoreOfSigma {true} pmOne bern[({true} : Set Bool).indicator 1 | ⊥] bern[pmOne | ⊥]
        bern[pmOne | ⊥] w) ^ 2 ∂bern ≤
    4 * (1 + (1 / 4 : ℝ)⁻¹) ^ 2 *
        (∫ w, (bern[pmOne | ⊥] w - (0 : ℝ)) ^ 2 ∂bern +
          ∫ w, (bern[pmOne | ⊥] w - (0 : ℝ)) ^ 2 ∂bern) +
      8 * 1 * ((1 / 4 : ℝ)⁻¹ * (1 / 2 : ℝ)⁻¹) ^ 2 *
        ∫ w, (bern[({true} : Set Bool).indicator (1 : Bool → ℝ) | ⊥] w - (1 / 4 : ℝ)) ^ 2 ∂bern :=
  integral_sq_aipwScoreOfSigma_sub_le (m := ⊥) (Y₀ := pmOne) (Y₁ := pmOne) bot_le
    (ae_of_all _ pmOne_observed) MemLp.of_discrete MemLp.of_discrete (by norm_num)
    (by rw [bern_propensity]; exact ae_of_all _ fun _ => by norm_num)
    (by rw [bern_pmOne_var]) (by rw [bern_pmOne_var]) stronglyMeasurable_const (memLp_const _)
    (memLp_const _) (by norm_num) (ae_of_all _ fun _ => by norm_num)

/-- Correct-nuisance boundary: `integral_sq_aipwScoreOfSigma_sub_le` applies at the true
nuisances `e = e*`, `g₀ = g₁ = μ*` of the `pmOne` fixture (with `ε = 1/2`), every error term on
its right side is `0`, so the bound forces the score error to be `0`. -/
example : ∫ w, (aipwScoreOfSigma {true} pmOne bern[({true} : Set Bool).indicator 1 | ⊥]
      bern[pmOne | ⊥] bern[pmOne | ⊥] w -
    aipwScoreOfSigma {true} pmOne bern[({true} : Set Bool).indicator 1 | ⊥] bern[pmOne | ⊥]
      bern[pmOne | ⊥] w) ^ 2 ∂bern = 0 := by
  have h := integral_sq_aipwScoreOfSigma_sub_le (m := ⊥) (Y₀ := pmOne) (Y₁ := pmOne)
    (e := bern[({true} : Set Bool).indicator 1 | ⊥]) (g₀ := bern[pmOne | ⊥])
    (g₁ := bern[pmOne | ⊥]) (C := 1) bot_le (ae_of_all _ pmOne_observed) MemLp.of_discrete
    MemLp.of_discrete (ε₀ := 1 / 2) (by norm_num)
    (by rw [bern_propensity]; exact ae_of_all _ fun _ => by norm_num) (by rw [bern_pmOne_var])
    (by rw [bern_pmOne_var]) stronglyMeasurable_condExp MemLp.of_discrete MemLp.of_discrete
    (ε := 1 / 2) (by norm_num) (by rw [bern_propensity]; exact ae_of_all _ fun _ => by norm_num)
  refine le_antisymm (h.trans (le_of_eq ?_)) (integral_nonneg fun _ => sq_nonneg _)
  simp

/-! ### Asymptotic normality from quarter rates -/

/-- `√n (c / (n + 1))² → 0`. -/
lemma tendsto_sqrt_mul_sq (c : ℝ) :
    Tendsto (fun n : ℕ => √(n : ℝ) * (c / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => c ^ 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (c ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => by positivity) fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : √(n : ℝ) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have key : √(n : ℝ) * (c / ((n : ℝ) + 1)) ^ 2 = c ^ 2 * (√(n : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    rw [div_pow]; ring
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg c)
  rw [div_le_div_iff₀ (by positivity) hn]
  nlinarith [mul_le_mul_of_nonneg_right hs hn.le]

/-- A deterministic sequence tending to `0` tends to `0` in probability. -/
lemma tendstoInMeasure_const_seq {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) :
    TendstoInMeasure bernSeq (fun n (_ : ℕ → Bool) => a n) atTop 0 :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (Eventually.of_forall fun _ => ha)

/-- Non-vacuity of `tendstoInDistribution_crossFit_aipw_of_quarter_rates`: i.i.d.
Bernoulli(1/2) treatment, trivial covariates, zero outcomes, a fitted propensity
`1/2 + (1/4)/(n+1)` (true value `1/2`) and a fitted treated-arm regression `1/(n+1)` (true
value `0`), both wrong at every `n` and both `o(n^{-1/4})`. The oracle score is `0`, so the limit
is the point mass at `0`. -/
example : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator (fun i ω => ω i) parity (fun n _ z =>
        aipwScoreOfSigma {true} (fun _ => (0 : ℝ)) (fun _ => 1 / 2 + (1 / 4) / ((n : ℝ) + 1))
          (fun _ => 0) (fun _ => 1 / ((n : ℝ) + 1)) z.2) n ω -
        ∫ w, ((fun _ : Bool => (0 : ℝ)) w - (fun _ : Bool => (0 : ℝ)) w) ∂bern))
      atTop (fun _ : Unit => (0 : ℝ)) (fun _ => bernSeq) (Measure.dirac ()) := by
  have hW : ∀ i, Measurable (fun ω : ℕ → Bool => ω i) := fun i => measurable_pi_apply i
  refine tendstoInDistribution_crossFit_aipw_of_quarter_rates (P := bernSeq) (ν := bern)
    (m := ⊥) (Y₀ := fun _ => 0) (Y₁ := fun _ => 0) (T := {true}) (Y := fun _ => 0) (K := 2)
    (ê := fun n _ _ _ => 1 / 2 + (1 / 4) / ((n : ℝ) + 1)) (ĝ₀ := fun _ _ _ _ => 0)
    (ĝ₁ := fun n _ _ _ => 1 / ((n : ℝ) + 1)) (C := 0) hW bernSeq_iIndep
    (fun i => ⟨(hW i).aemeasurable, (hW 0).aemeasurable,
      (bernSeq_map i).trans (bernSeq_map 0).symm⟩)
    (bernSeq_map 0) bot_le (measurableSet_singleton _) measurable_const
    (Eventually.of_forall fun w => by cases w <;> simp [observed])
    (memLp_const _) (memLp_const _) ?_ ?_ (ε₀ := 1 / 2) (by norm_num) ?_ ?_ ?_ parity
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    (fun _ _ _ => stronglyMeasurable_const) (fun _ _ _ => stronglyMeasurable_const)
    (fun _ _ _ => stronglyMeasurable_const) (fun _ _ _ => memLp_const _)
    (fun _ _ _ => memLp_const _) (ε := 1 / 4) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x => by simp
  · exact Eventually.of_forall fun x => by simp
  · rw [bern_propensity]; exact Eventually.of_forall fun _ => by norm_num
  · simp; exact Eventually.of_forall fun _ => le_rfl
  · simp; exact Eventually.of_forall fun _ => le_rfl
  · intro n _ _ _
    have h : (1 / 4 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 4 :=
      div_le_self (by norm_num) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    have h0 : 0 ≤ (1 / 4 : ℝ) / ((n : ℝ) + 1) := by positivity
    constructor <;> linarith
  · intro k
    have hf : (fun (n : ℕ) (ω : ℕ → Bool) => √(n : ℝ) *
        ∫ w, (bern[({true} : Set Bool).indicator 1 | ⊥] w -
          (fun n _ _ _ => 1 / 2 + (1 / 4) / ((n : ℝ) + 1) : (n : ℕ) → Fin 2 →
            (trainFold parity n k → Bool) → Bool → ℝ) n k
              (trainData (fun i ω => ω i) parity n k ω) w) ^ 2 ∂bern) =
        fun (n : ℕ) (_ : ℕ → Bool) => √(n : ℝ) * ((1 / 4) / ((n : ℝ) + 1)) ^ 2 := by
      funext n ω
      rw [bern_propensity, integral_bern]
      ring
    rw [hf]
    exact tendstoInMeasure_const_seq (tendsto_sqrt_mul_sq _)
  · intro k
    simp only [bern_regression, Pi.zero_apply, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, mul_zero]
    exact tendstoInMeasure_const_seq tendsto_const_nhds
  · intro k
    have hf : (fun (n : ℕ) (ω : ℕ → Bool) => √(n : ℝ) *
        ∫ w, (bern[(fun _ : Bool => (0 : ℝ)) | ⊥] w -
          (fun n _ _ _ => 1 / ((n : ℝ) + 1) : (n : ℕ) → Fin 2 →
            (trainFold parity n k → Bool) → Bool → ℝ) n k
              (trainData (fun i ω => ω i) parity n k ω) w) ^ 2 ∂bern) =
        fun (n : ℕ) (_ : ℕ → Bool) => √(n : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2 := by
      funext n ω
      rw [bern_regression, integral_bern]
      simp only [Pi.zero_apply, zero_sub, neg_sq]
      ring
    rw [hf]
    exact tendstoInMeasure_const_seq (tendsto_sqrt_mul_sq _)
  · rw [bern_oracle_score, variance_zero, Real.toNNReal_zero, gaussianReal_zero_var]
    exact ⟨aemeasurable_const, by simp⟩

end MathlibExtTest.Probability.Causality.AugmentedIPW.DoubleMLRates
