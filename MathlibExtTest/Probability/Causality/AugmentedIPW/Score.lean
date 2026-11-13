/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.Score
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tests for the AIPW score with fixed nuisance functions

* Smoke test and explicit values: a binary covariate and a binary treatment (`Ω = Bool × Bool`),
  fixed candidate functions `e, m₀, m₁`, and the score computed on all four units. At
  `(true, true)` and `(true, false)` the score differs from both the regression contrast and the
  IPW contrast, so the definition is not vacuous; the augmented-IPW and potential-outcome forms
  are checked on the same units.
* The score and its integral are definitionally equal to the canonical `MissingOutcomes` API.
* Junk values: candidate propensities `e = 0` and `e = 1` drop their respective residuals.
* A fair coin with a constant covariate witnesses `AIPWAssumptions` and
  instantiates the correct-propensity lemma.
* Independent outcome and treatment coins exercise both correct-outcome lemmas
  with a wrong candidate propensity. Their residuals are nonzero on units of
  positive mass but cancel in conditional expectation.
-/

@[expose] public section

open MeasureTheory Filter MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Causality.AugmentedIPW

/-! ### Canonical API compatibility -/

example {Ω 𝒳 : Type*} (T : Set Ω) (X : Ω → 𝒳) (Y : Ω → ℝ) (e m₀ m₁ : 𝒳 → ℝ) :
    aipwScore T X Y e m₀ m₁ = MissingOutcomes.aipwATEScore T X e m₀ m₁ Y := rfl

example {Ω 𝒳 : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳)
    (Y : Ω → ℝ) (e m₀ m₁ : 𝒳 → ℝ) :
    (∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ) =
      ∫ ω, MissingOutcomes.aipwATEScore T X e m₀ m₁ Y ω ∂μ := rfl

/-! ### Smoke test: the score on a finite covariate space -/

/-- Units are pairs (covariate, treatment). -/
abbrev Unit₂ := Bool × Bool

/-- Treated units. -/
def treated : Set Unit₂ := {ω | ω.2 = true}

/-- The covariate. -/
def cov : Unit₂ → Bool := Prod.fst

/-- Candidate propensity: `3/4` at `x = true`, `1/2` at `x = false`. -/
noncomputable def e₀ (x : Bool) : ℝ := if x then 3 / 4 else 1 / 2

/-- Candidate control regression. -/
noncomputable def r₀ (x : Bool) : ℝ := if x then 1 else 0

/-- Candidate treated regression. -/
noncomputable def r₁ (x : Bool) : ℝ := if x then 3 else 2

/-- Observed outcomes. -/
noncomputable def obs : Unit₂ → ℝ
  | (true, true) => 5
  | (true, false) => 2
  | (false, true) => 1
  | (false, false) => 0

/-- Smoke test, straight from the definition: `2 + (5 - 3) / (3/4) = 14/3`. -/
example : aipwScore treated cov obs e₀ r₀ r₁ (true, true) = 14 / 3 := by
  simp [aipwScore_eq, treated, cov, obs, e₀, r₀, r₁]
  norm_num

example : aipwScore treated cov obs e₀ r₀ r₁ (true, false) = -2 := by
  rw [aipwScore_of_notMem (by simp [treated])]
  norm_num [cov, obs, e₀, r₀, r₁]

example : aipwScore treated cov obs e₀ r₀ r₁ (false, true) = 0 := by
  rw [aipwScore_of_mem (by simp [treated])]
  norm_num [cov, obs, e₀, r₀, r₁]

example : aipwScore treated cov obs e₀ r₀ r₁ (false, false) = 2 := by
  rw [aipwScore_of_notMem (by simp [treated])]
  norm_num [cov, obs, e₀, r₀, r₁]

/-- Non-vacuity: the score differs from the regression contrast `r₁ - r₀ = 2`. -/
example : aipwScore treated cov obs e₀ r₀ r₁ (true, true) ≠ r₁ (cov (true, true)) -
    r₀ (cov (true, true)) := by
  rw [aipwScore_of_mem (by simp [treated])]
  norm_num [cov, obs, e₀, r₀, r₁]

/-- Non-vacuity: the score differs from the IPW contrast `5 / (3/4) = 20/3`. -/
example : aipwScore treated cov obs e₀ r₀ r₁ (true, true) ≠
    treated.indicator (fun ω => obs ω / e₀ (cov ω)) (true, true) -
      treatedᶜ.indicator (fun ω => obs ω / (1 - e₀ (cov ω))) (true, true) := by
  rw [aipwScore_of_mem (by simp [treated])]
  simp [treated, cov, obs, e₀, r₀, r₁]
  norm_num

/-- Non-vacuity on a control unit: the score `-2` differs from the regression contrast `2`. -/
example : aipwScore treated cov obs e₀ r₀ r₁ (true, false) ≠ r₁ (cov (true, false)) -
    r₀ (cov (true, false)) := by
  rw [aipwScore_of_notMem (by simp [treated])]
  norm_num [cov, obs, e₀, r₀, r₁]

/-- Non-vacuity on a control unit: the score `-2` differs from the IPW contrast
`-2 / (1/4) = -8`. -/
example : aipwScore treated cov obs e₀ r₀ r₁ (true, false) ≠
    treated.indicator (fun ω => obs ω / e₀ (cov ω)) (true, false) -
      treatedᶜ.indicator (fun ω => obs ω / (1 - e₀ (cov ω))) (true, false) := by
  rw [aipwScore_of_notMem (by simp [treated])]
  simp [treated, cov, obs, e₀, r₀, r₁]
  norm_num

/-- The augmented-IPW form on a control unit: IPW contrast `-2 / (1/4) = -8`, propensity residual
`-3/4`, coefficient `3 / (3/4) + 1 / (1/4) = 8`, so `-8 - (-3/4) * 8 = -2`. -/
example : treated.indicator (fun ω => obs ω / e₀ (cov ω)) (true, false) -
      treatedᶜ.indicator (fun ω => obs ω / (1 - e₀ (cov ω))) (true, false) -
        (treated.indicator 1 (true, false) - e₀ (cov (true, false))) *
          (r₁ (cov (true, false)) / e₀ (cov (true, false)) +
            r₀ (cov (true, false)) / (1 - e₀ (cov (true, false)))) = -2 := by
  rw [← aipwScore_eq_ipw_sub (by norm_num [cov, e₀]) (by norm_num [cov, e₀])]
  rw [aipwScore_of_notMem (by simp [treated])]
  norm_num [cov, obs, e₀, r₀, r₁]

/-- Potential outcomes consistent with `obs`: `Y₁` agrees with `obs` on treated units. -/
noncomputable def pot₁ (ω : Unit₂) : ℝ := obs (ω.1, true)

/-- Potential outcomes consistent with `obs`: `Y₀` agrees with `obs` on control units. -/
noncomputable def pot₀ (ω : Unit₂) : ℝ := obs (ω.1, false)

lemma obs_consistent : ∀ ω, obs ω = observed treated pot₀ pot₁ ω := by
  rintro ⟨x, t⟩
  cases t <;> simp [observed, treated, pot₀, pot₁]

/-- Under consistency the treated residual uses `Y₁`: at `(true, true)` it is
`2 + (pot₁ - 3) / (3/4) = 14/3`. -/
example : aipwScore treated cov obs e₀ r₀ r₁ (true, true) = 14 / 3 := by
  rw [aipwScore_eq_of_consistency obs_consistent]
  simp [treated, cov, pot₁, obs, e₀, r₀, r₁]
  norm_num

/-! ### Junk value -/

/-- A candidate propensity `0` makes the treated residual `(Y - m₁) / 0 = 0`: the score of a
treated unit is then the regression contrast. Positivity of the candidate rules this out. -/
example : aipwScore treated cov obs (fun _ => 0) r₀ r₁ (true, true) = 2 := by
  rw [aipwScore_of_mem (by simp [treated])]
  norm_num [cov, r₀, r₁]

/-- A candidate propensity `1` drops the control residual at a control unit. -/
example : aipwScore treated cov obs (fun _ => 1) r₀ r₁ (true, false) = 2 := by
  rw [aipwScore_of_notMem (by simp [treated])]
  norm_num [cov, r₀, r₁]

/-! ### A witness of the assumptions: a fair coin with a constant covariate -/

/-- A fair coin. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

lemma coin_apply_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  cases b <;> simp [coin]

instance : IsProbabilityMeasure coin := by
  constructor
  rw [show (Set.univ : Set Bool) = {true} ∪ {false} by ext b; cases b <;> simp,
    measure_union (by simp) (measurableSet_singleton _), coin_apply_singleton,
    coin_apply_singleton, ENNReal.inv_two_add_inv_two]

lemma integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  rw [integral_fintype (.of_finite)]
  simp [measureReal_def, coin_apply_singleton]
  ring

/-- The treated event of the coin. -/
def heads : Set Bool := {true}

/-- The constant covariate. -/
def noCov : Bool → Unit := fun _ => ()

lemma condExp_noCov (f : Bool → ℝ) :
    coin[f | MeasurableSpace.comap noCov inferInstance] = fun _ => (f true + f false) / 2 := by
  rw [show MeasurableSpace.comap noCov inferInstance = ⊥ from MeasurableSpace.comap_const _,
    condExp_bot, integral_coin]

/-- Consistency, mean exchangeability and positivity hold for the fair coin with constant
potential outcomes `Y₀ = 1`, `Y₁ = 3` (true propensity `1/2`). -/
theorem coin_assumptions :
    AIPWAssumptions coin heads noCov (observed heads (fun _ => 1) (fun _ => 3)) (fun _ => 1)
      (fun _ => 3) where
  consistency _ := rfl
  meanExch_treated := Eventually.of_forall fun _ => by
    simp only [condExp_noCov, Pi.mul_apply]
    simp [heads]
    norm_num
  meanExch_control := Eventually.of_forall fun _ => by
    simp only [condExp_noCov, Pi.mul_apply]
    simp [heads]
  positivity := ⟨1 / 4, by norm_num, Eventually.of_forall fun _ => by
    simp only [condExp_noCov]
    simp [heads]
    norm_num⟩

lemma propensity_noCov :
    coin[heads.indicator (1 : Bool → ℝ) | MeasurableSpace.comap noCov inferInstance] =ᵐ[coin]
      fun ω => (fun _ : Unit => (1 / 2 : ℝ)) (noCov ω) :=
  Eventually.of_forall fun _ => by
    simp only [condExp_noCov]
    simp [heads]

/-- The correct-propensity lemma instantiated with the true propensity `1/2`. -/
example : coin[fun ω => (heads.indicator 1 ω - (fun _ : Unit => (1 / 2 : ℝ)) (noCov ω)) *
      (fun _ : Unit => (7 : ℝ)) (noCov ω) | MeasurableSpace.comap noCov inferInstance] =ᵐ[coin]
      0 :=
  condExp_propensityResidual_mul (measurableSet_singleton _) measurable_const measurable_const
    measurable_const (C := 7) (fun _ => by norm_num) propensity_noCov

/-! ### Varying potential outcomes independent of treatment -/

private noncomputable def pairCoin : Measure Unit₂ := coin.prod coin

private instance : IsProbabilityMeasure pairCoin := by
  dsimp [pairCoin]
  infer_instance

private lemma integral_pairCoin (f : Unit₂ → ℝ) :
    ∫ ω, f ω ∂pairCoin =
      (f (true, true) + f (true, false) +
        f (false, true) + f (false, false)) / 4 := by
  rw [pairCoin, integral_prod _ (.of_finite), integral_coin]
  simp_rw [integral_coin]
  ring

private def pairNoCov : Unit₂ → Unit := fun _ => ()

private lemma condExp_pairNoCov (f : Unit₂ → ℝ) :
    pairCoin[f | MeasurableSpace.comap pairNoCov inferInstance] =
      fun _ => (f (true, true) + f (true, false) +
        f (false, true) + f (false, false)) / 4 := by
  rw [show MeasurableSpace.comap pairNoCov inferInstance = ⊥ from
    MeasurableSpace.comap_const _, condExp_bot, integral_pairCoin]

private noncomputable def varyingControl (ω : Unit₂) : ℝ :=
  if ω.1 then 2 else 0

private noncomputable def varyingTreated (ω : Unit₂) : ℝ :=
  if ω.1 then 4 else 2

private theorem pair_assumptions :
    AIPWAssumptions pairCoin treated pairNoCov
      (observed treated varyingControl varyingTreated)
      varyingControl varyingTreated where
  consistency _ := rfl
  meanExch_treated := Eventually.of_forall fun _ => by
    norm_num [condExp_pairNoCov, Pi.mul_apply, treated, varyingTreated]
  meanExch_control := Eventually.of_forall fun _ => by
    norm_num [condExp_pairNoCov, Pi.mul_apply, treated, varyingControl]
  positivity := ⟨1 / 4, by norm_num, Eventually.of_forall fun _ => by
    norm_num [condExp_pairNoCov, treated]⟩

private noncomputable def treatedResidual : Unit₂ → ℝ :=
  treated.indicator (fun ω =>
    (observed treated varyingControl varyingTreated ω - 3) / (1 / 3))

/-- Correct outcome regression cancels a varying treated residual even with
candidate propensity `1/3`, rather than the true propensity `1/2`. -/
private theorem treated_residual_condExp :
    pairCoin[treatedResidual |
      MeasurableSpace.comap pairNoCov inferInstance] =ᵐ[pairCoin] 0 :=
  pair_assumptions.condExp_outcomeResidual_treated
    (e := fun _ => 1 / 3) (m₁ := fun _ => 3) (ε := 1 / 3)
    (Set.toFinite _).measurableSet measurable_const (.of_finite)
    measurable_const measurable_const (by norm_num) (fun _ => le_rfl)
    (Eventually.of_forall fun _ => by
      norm_num [condExp_pairNoCov, varyingTreated])

private noncomputable def controlResidual : Unit₂ → ℝ :=
  treatedᶜ.indicator (fun ω =>
    (observed treated varyingControl varyingTreated ω - 1) / (1 - 1 / 3))

/-- The control-arm residual also cancels in conditional expectation. -/
private theorem control_residual_condExp :
    pairCoin[controlResidual |
      MeasurableSpace.comap pairNoCov inferInstance] =ᵐ[pairCoin] 0 :=
  pair_assumptions.condExp_outcomeResidual_control
    (e := fun _ => 1 / 3) (m₀ := fun _ => 1) (ε := 2 / 3)
    (Set.toFinite _).measurableSet measurable_const (.of_finite)
    measurable_const measurable_const (by norm_num) (fun _ => by norm_num)
    (Eventually.of_forall fun _ => by
      norm_num [condExp_pairNoCov, varyingControl])

/-- Each residual takes opposite nonzero values on its own treatment arm,
and vanishes on the other arm. -/
example : treatedResidual (true, true) = 3 ∧
    treatedResidual (false, true) = -3 ∧
    treatedResidual (true, false) = 0 ∧ treatedResidual (false, false) = 0 := by
  norm_num [treatedResidual, treated, observed, varyingControl, varyingTreated]

example : controlResidual (true, false) = 3 / 2 ∧
    controlResidual (false, false) = -3 / 2 ∧
    controlResidual (true, true) = 0 ∧ controlResidual (false, true) = 0 := by
  norm_num [controlResidual, treated, observed, varyingControl, varyingTreated]

/-- All four units have positive mass, so the nonzero residuals are not null events. -/
example (x t : Bool) : pairCoin {(x, t)} = 1 / 4 := by
  rw [show {(x, t)} = ({x} : Set Bool) ×ˢ {t} by ext ω; simp,
    pairCoin, Measure.prod_prod, coin_apply_singleton, coin_apply_singleton]
  norm_num [← ENNReal.mul_inv]

#print axioms pair_assumptions
#print axioms treated_residual_condExp
#print axioms control_residual_condExp

end MathlibExtTest.Probability.Causality.AugmentedIPW

#print axioms aipwScore_eq
#print axioms aipwScore_eq_of_consistency
#print axioms aipwScore_eq_ipw_sub
#print axioms condExp_propensityResidual_mul
#print axioms condExp_outcomeResidual_treated
#print axioms condExp_outcomeResidual_control
#print axioms AIPWAssumptions.condExp_outcomeResidual_treated
#print axioms AIPWAssumptions.condExp_outcomeResidual_control
#print axioms MathlibExtTest.Probability.Causality.AugmentedIPW.coin_assumptions
