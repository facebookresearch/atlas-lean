/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.HahnVariance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Tests for Hahn's variance formula and efficiency in the augmented IPW class

* A fully discharged witness of `HahnSetup`: two independent fair coins, the second one the
  treatment and the first one the outcome noise, with a constant covariate. The potential
  outcomes `Y₁ ∈ {3, 1}` and `Y₀ ∈ {1, 0}` have conditional variances `1` and `1/4`, so both
  variance terms of Hahn's bound are nonzero; the bound is `1 / (1/2) + (1/4) / (1/2) = 5/2`.
* The variance of the AIPW score, `5/2`, and of the IPW score (augmentation `0`), `35/4`, are
  computed directly from the definitions by summing over the four units, independently of the
  theorems under test. The theorems are then instantiated and agree with these values; the
  IPW score is strictly less efficient, so the efficiency inequality is not vacuous.
* The covariate term `(τ(X) - τ)²` of `hahnBound` is evaluated on a non-constant covariate.
* The AIPW score coincides with the augmented IPW score at the efficient augmentation on a
  unit-level example, and augmentation `0` gives the IPW contrast.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.AugmentedIPW.HahnVariance

namespace MathlibExtTest.Probability.Causality.AugmentedIPW.HahnVariance

/-! ### Two fair coins -/

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

/-- Units are pairs (outcome noise, treatment). -/
abbrev Unit₂ := Bool × Bool

/-- Two independent fair coins. -/
noncomputable def pairCoin : Measure Unit₂ := coin.prod coin

instance : IsProbabilityMeasure pairCoin := by
  dsimp [pairCoin]
  infer_instance

lemma integral_pairCoin (f : Unit₂ → ℝ) :
    ∫ ω, f ω ∂pairCoin =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  rw [pairCoin, integral_prod _ (.of_finite), integral_coin]
  simp_rw [integral_coin]
  ring

/-- The treated event: the second coin shows heads. -/
def treated : Set Unit₂ := {ω | ω.2 = true}

/-- The constant covariate. -/
def noCov : Unit₂ → Unit := fun _ => ()

lemma condExp_noCov (f : Unit₂ → ℝ) :
    pairCoin[f | MeasurableSpace.comap noCov inferInstance] =
      fun _ => (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  rw [show MeasurableSpace.comap noCov inferInstance = ⊥ from MeasurableSpace.comap_const _,
    condExp_bot, integral_pairCoin]

/-! ### The witness -/

/-- Treated potential outcome: `3` or `1` by the noise coin (mean `2`, variance `1`). -/
noncomputable def pot₁ (ω : Unit₂) : ℝ := if ω.1 then 3 else 1

/-- Control potential outcome: `1` or `0` by the noise coin (mean `1/2`, variance `1/4`). -/
noncomputable def pot₀ (ω : Unit₂) : ℝ := if ω.1 then 1 else 0

/-- The observed outcome. -/
noncomputable def obs : Unit₂ → ℝ := observed treated pot₀ pot₁

/-- The true propensity `1/2`. -/
noncomputable def eTrue : Unit → ℝ := fun _ => 1 / 2

/-- The true treated regression `2`. -/
noncomputable def m₁True : Unit → ℝ := fun _ => 2

/-- The true control regression `1/2`. -/
noncomputable def m₀True : Unit → ℝ := fun _ => 1 / 2

/-- The treated conditional variance `1`. -/
noncomputable def s₁True : Unit → ℝ := fun _ => 1

/-- The control conditional variance `1/4`. -/
noncomputable def s₀True : Unit → ℝ := fun _ => 1 / 4

lemma memLp_finite (f : Unit₂ → ℝ) : MemLp f 2 pairCoin :=
  memLp_top_of_bound (measurable_of_finite f).aestronglyMeasurable
    (∑ ω : Unit₂, ‖f ω‖) (Eventually.of_forall fun ω =>
      Finset.single_le_sum (f := fun ω => ‖f ω‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ ω)) |>.mono_exponent le_top

/-- All assumptions of Hahn's formula hold for the two-coin model. -/
theorem coin_hahnSetup :
    HahnSetup pairCoin treated noCov obs pot₀ pot₁ eTrue m₀True m₁True s₀True s₁True where
  measurableSet_T := (Set.toFinite _).measurableSet
  measurable_X := measurable_const
  consistency _ := rfl
  memLp_Y₀ := memLp_finite _
  memLp_Y₁ := memLp_finite _
  measurable_e := measurable_const
  measurable_m₀ := measurable_const
  measurable_m₁ := measurable_const
  overlap := ⟨1 / 4, by norm_num, fun _ => by norm_num [eTrue]⟩
  propensity := Eventually.of_forall fun _ => by norm_num [condExp_noCov, treated, eTrue]
  regression₀ := Eventually.of_forall fun _ => by norm_num [condExp_noCov, pot₀, m₀True]
  regression₁ := Eventually.of_forall fun _ => by norm_num [condExp_noCov, pot₁, m₁True]
  condVar₀ := Eventually.of_forall fun _ => by norm_num [condExp_noCov, pot₀, m₀True, s₀True]
  condVar₁ := Eventually.of_forall fun _ => by norm_num [condExp_noCov, pot₁, m₁True, s₁True]
  meanExch₀ := Eventually.of_forall fun _ => by
    norm_num [condExp_noCov, Pi.mul_apply, treated, pot₀]
  meanExch₁ := Eventually.of_forall fun _ => by
    norm_num [condExp_noCov, Pi.mul_apply, treated, pot₁]
  varExch₀ := Eventually.of_forall fun _ => by
    norm_num [condExp_noCov, Pi.mul_apply, treated, pot₀, m₀True]
  varExch₁ := Eventually.of_forall fun _ => by
    norm_num [condExp_noCov, Pi.mul_apply, treated, pot₁, m₁True]

/-! ### Values computed from the definitions -/

/-- The average treatment effect is `2 - 1/2 = 3/2`. -/
lemma ate_coin : ∫ ω, (pot₁ ω - pot₀ ω) ∂pairCoin = 3 / 2 := by
  rw [integral_pairCoin]; norm_num [pot₁, pot₀]

/-- Hahn's bound for the two-coin model is `1 / (1/2) + (1/4) / (1/2) + 0 = 5/2`. -/
lemma hahnBound_coin :
    hahnBound pairCoin noCov eTrue m₀True m₁True s₀True s₁True (3 / 2) = 5 / 2 := by
  rw [hahnBound, integral_pairCoin]; norm_num [eTrue, m₀True, m₁True, s₀True, s₁True]

/-- The AIPW score on the four units: `7/2, 1/2, -1/2, 5/2`. -/
lemma aipwScore_coin_values :
    aipwScore treated noCov obs eTrue m₀True m₁True (true, true) = 7 / 2 ∧
    aipwScore treated noCov obs eTrue m₀True m₁True (true, false) = 1 / 2 ∧
    aipwScore treated noCov obs eTrue m₀True m₁True (false, true) = -1 / 2 ∧
    aipwScore treated noCov obs eTrue m₀True m₁True (false, false) = 5 / 2 := by
  simp only [aipwScore_eq]
  norm_num [treated, obs, observed, pot₀, pot₁, eTrue, m₀True, m₁True]

/-- Direct computation, without the theorem under test: `Var(ψ) = 5/2`
(deviations `2, -1, -2, 1` from the mean `3/2`). -/
lemma variance_aipwScore_coin_direct :
    Var[aipwScore treated noCov obs eTrue m₀True m₁True; pairCoin] = 5 / 2 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := aipwScore_coin_values
  rw [variance_eq_integral (.of_discrete), integral_pairCoin, h₁, h₂, h₃, h₄,
    integral_pairCoin, h₁, h₂, h₃, h₄]
  norm_num

/-- The IPW score (augmentation `0`) on the four units: `6, -2, 2, 0`. -/
lemma ipwScore_coin_values :
    augmentedIPWScore treated noCov obs eTrue (fun _ => 0) (true, true) = 6 ∧
    augmentedIPWScore treated noCov obs eTrue (fun _ => 0) (true, false) = -2 ∧
    augmentedIPWScore treated noCov obs eTrue (fun _ => 0) (false, true) = 2 ∧
    augmentedIPWScore treated noCov obs eTrue (fun _ => 0) (false, false) = 0 := by
  simp only [augmentedIPWScore]
  norm_num [treated, obs, observed, pot₀, pot₁, eTrue]

/-- Direct computation, without the theorem under test: `Var(IPW) = 11 - (3/2)² = 35/4`. -/
lemma variance_ipwScore_coin_direct :
    Var[augmentedIPWScore treated noCov obs eTrue (fun _ => 0); pairCoin] = 35 / 4 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := ipwScore_coin_values
  rw [variance_eq_integral (.of_discrete), integral_pairCoin, h₁, h₂, h₃, h₄,
    integral_pairCoin, h₁, h₂, h₃, h₄]
  norm_num

/-! ### The theorems on the witness -/

/-- Hahn's formula on the witness: `Var(ψ) = hahnBound … τ`, which is `5/2`, matching the
direct computation. -/
example : Var[aipwScore treated noCov obs eTrue m₀True m₁True; pairCoin] = 5 / 2 := by
  rw [coin_hahnSetup.variance_aipwScore, ate_coin, hahnBound_coin]

/-- The mean identity on the witness. -/
example : ∫ ω, aipwScore treated noCov obs eTrue m₀True m₁True ω ∂pairCoin = 3 / 2 := by
  rw [coin_hahnSetup.integral_aipwScore, ate_coin]

/-- The IPW score is unbiased on the witness. -/
example : ∫ ω, augmentedIPWScore treated noCov obs eTrue (fun _ => 0) ω ∂pairCoin = 3 / 2 := by
  rw [coin_hahnSetup.integral_augmentedIPWScore measurable_const (memLp_const 0), ate_coin]

/-- The variance gap on the witness: `E[e(1 - e)(h* - 0)²] = (1/4) · 5² = 25/4`, and
`5/2 + 25/4 = 35/4`, matching the direct computation. -/
example : Var[augmentedIPWScore treated noCov obs eTrue (fun _ => 0); pairCoin] = 35 / 4 := by
  rw [coin_hahnSetup.variance_augmentedIPWScore measurable_const (memLp_const 0),
    variance_aipwScore_coin_direct, integral_pairCoin]
  norm_num [efficientAugmentation, eTrue, m₀True, m₁True]

/-- The efficiency inequality on the witness, with a strict gap: the IPW score has variance
`35/4`, strictly above Hahn's bound `5/2`. -/
example : hahnBound pairCoin noCov eTrue m₀True m₁True s₀True s₁True
      (∫ ω, (pot₁ ω - pot₀ ω) ∂pairCoin) <
    Var[augmentedIPWScore treated noCov obs eTrue (fun _ => 0); pairCoin] := by
  have := coin_hahnSetup.hahnBound_le_variance_augmentedIPWScore measurable_const
    (memLp_const (0 : ℝ))
  rw [ate_coin, hahnBound_coin, variance_ipwScore_coin_direct]
  norm_num

/-! ### The covariate term of Hahn's bound -/

/-- With the covariate `X = ω.1`, zero conditional variances and `τ(X) ∈ {3, 1}`, Hahn's
expression at `τ = 2` is the covariate term alone, `E[(τ(X) - 2)²] = 1`. -/
example : hahnBound pairCoin Prod.fst (fun _ => 1 / 2) (fun _ => 0) (fun x => if x then 3 else 1)
    (fun _ => 0) (fun _ => 0) 2 = 1 := by
  rw [hahnBound, integral_pairCoin]; norm_num

/-! ### Unit-level identities -/

/-- On a covariate-dependent example, the AIPW score equals the augmented IPW score at the
efficient augmentation (checked on a control unit: `-2` both ways). -/
example : aipwScore treated Prod.fst (fun ω => if ω.1 then 2 else 0)
      (fun x => if x then 3 / 4 else 1 / 2) (fun x => if x then 1 else 0)
      (fun x => if x then 3 else 2) (true, false) =
    augmentedIPWScore treated Prod.fst (fun ω => if ω.1 then 2 else 0)
      (fun x => if x then 3 / 4 else 1 / 2)
      (efficientAugmentation (fun x => if x then 3 / 4 else 1 / 2) (fun x => if x then 1 else 0)
        (fun x => if x then 3 else 2)) (true, false) := by
  simp only [aipwScore_eq, augmentedIPWScore, efficientAugmentation]
  norm_num [treated]

/-- Augmentation `0` gives the IPW contrast. -/
example {Ω 𝒳 : Type*} (T : Set Ω) (X : Ω → 𝒳) (Y : Ω → ℝ) (e : 𝒳 → ℝ) (ω : Ω) :
    augmentedIPWScore T X Y e (fun _ => 0) ω =
      T.indicator (fun ω => Y ω / e (X ω)) ω - Tᶜ.indicator (fun ω => Y ω / (1 - e (X ω))) ω := by
  simp [augmentedIPWScore]

#print axioms coin_hahnSetup
#print axioms variance_aipwScore_coin_direct
#print axioms variance_ipwScore_coin_direct

end MathlibExtTest.Probability.Causality.AugmentedIPW.HahnVariance

#print axioms HahnSetup.integral_aipwScore
#print axioms HahnSetup.integral_sq_aipwScore_sub
#print axioms HahnSetup.variance_aipwScore
#print axioms HahnSetup.aipwScore_eq_augmentedIPWScore
#print axioms HahnSetup.integral_augmentedIPWScore
#print axioms HahnSetup.variance_augmentedIPWScore
#print axioms HahnSetup.hahnBound_le_variance_augmentedIPWScore
