/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.Identification
public import MathlibExtTest.Probability.Causality.CausalIdentification

/-!
# Tests for identification of a mean with a missing outcome

The probability space is two independent fair coins, `Ω = Bool × Bool`.

* MCAR witness: the response event is the first coin, the covariate and outcome are functions of
  the second coin; complete-case identification applies (with the observed-data property of the
  complete-case mean checked on it), and so does the general-covariate IPW identity with the
  trivial σ-algebra.
* MAR witness: the response probability depends on the covariate, equal to `1` in one stratum,
  so positivity holds without an upper bound and the IPW identity applies.
* Boundaries: no respondents (the complete-case mean is the junk value `0` although MCAR holds
  vacuously), and positivity failure (MAR holds but the IPW mean is not `E[Y]`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.MissingData MathlibExtTest.Probability.Causality

namespace MathlibExtTest.Probability.Causality.MissingData

/-- Two independent fair coins. -/
noncomputable def coins : Measure (Bool × Bool) := coin.prod coin

instance : IsProbabilityMeasure coins := by
  unfold coins; infer_instance

lemma coins_real_prod (s t : Set Bool) :
    coins.real (s ×ˢ t) = coin.real s * coin.real t := by
  rw [coins, measureReal_prod_prod]

lemma coin_real_univ : coin.real Set.univ = 1 := coin_univ

lemma coins_real_singleton (ω : Bool × Bool) : coins.real {ω} = 1 / 4 := by
  rw [← Set.singleton_prod_singleton, coins_real_prod, coin_singleton, coin_singleton]
  norm_num

/-- The response event: the first coin shows `true`. -/
def resp : Set (Bool × Bool) := {true} ×ˢ Set.univ

lemma measurableSet_resp : MeasurableSet resp :=
  (measurableSet_singleton true).prod MeasurableSet.univ

lemma coins_real_resp : coins.real resp = 1 / 2 := by
  rw [resp, coins_real_prod, coin_singleton, coin_real_univ, mul_one]

/-! ### MCAR witness -/

/-- **Non-vacuity of MCAR**: the first coin is independent of every function of the second
coin. -/
theorem mcar_resp {β : Type*} [MeasurableSpace β] (h : Bool → β) :
    CondIndepDiscrete coins resp (fun ω => h ω.2) (fun _ => ()) := by
  intro B _ w
  have h1 : resp ∩ (fun ω : Bool × Bool => h ω.2) ⁻¹' B = {true} ×ˢ (h ⁻¹' B) := by
    ext ⟨a, b⟩; simp [resp]
  have h2 : (fun ω : Bool × Bool => h ω.2) ⁻¹' B = Set.univ ×ˢ (h ⁻¹' B) := by
    ext ⟨a, b⟩; simp
  simp only [Set.preimage_const, Set.mem_singleton_iff, ↓reduceIte, Set.inter_univ,
    probReal_univ, mul_one]
  rw [h1, h2, coins_real_prod, coins_real_prod, coins_real_resp, coin_singleton, coin_real_univ,
    one_mul]

/-- Complete-case identification on the witness: covariate `X = ω.2`, outcome `Y = g ω.2`. -/
example (g : Bool → ℝ) :
    completeCaseMean coins resp (fun ω => g ω.2) = ∫ ω, g ω.2 ∂coins :=
  completeCaseMean_eq_integral_of_mcar measurableSet_resp (X := fun ω => ω.2)
    (measurable_of_finite _) (mcar_resp fun b => (b, g b)) (by rw [coins_real_resp]; norm_num)

/-- The same identity as the mean under the conditional law given response. -/
example (g : Bool → ℝ) :
    ∫ ω, g ω.2 ∂(coins[|resp]) = ∫ ω, g ω.2 ∂coins :=
  integral_cond_eq_integral_of_mcar measurableSet_resp (X := fun ω => ω.2)
    (measurable_of_finite _) (mcar_resp fun b => (b, g b)) (by rw [coins_real_resp]; norm_num)

/-- The complete-case mean is an observed-data estimand: changing the outcome off the response
event does not change it. -/
example (g : Bool → ℝ) (c : ℝ) :
    completeCaseMean coins resp (fun ω => if ω.1 then g ω.2 else c) =
      completeCaseMean coins resp (fun ω => g ω.2) :=
  completeCaseMean_congr fun ω hω => by simp [show ω.1 = true from hω.1]

/-- **Non-vacuity** of the general-covariate IPW identity: the trivial σ-algebra, with mean MAR
supplied by the MCAR factorization `E[1_R Y] = P(R) E[Y]` and strong positivity `ε = 1/2`. -/
example (g : Bool → ℝ) :
    ∫ ω, resp.indicator (fun ω => g ω.2 / coins[resp.indicator 1 | ⊥] ω) ω ∂coins =
      ∫ ω, g ω.2 ∂coins := by
  have hR : ∫ ω, resp.indicator (1 : Bool × Bool → ℝ) ω ∂coins = 1 / 2 := by
    rw [Pi.one_def, integral_indicator_const _ measurableSet_resp, coins_real_resp, smul_eq_mul,
      mul_one]
  refine integral_ipw_eq_integral_of_mar_condExp bot_le measurableSet_resp
    (Integrable.of_finite) ?_ (by norm_num : (0 : ℝ) < 1 / 2) ?_
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [condExp_bot]
    rw [hR, integral_indicator_eq_measureReal_mul_of_indep measurableSet_resp
      (measurable_of_finite _) (mcar_resp g), coins_real_resp]
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [condExp_bot]
    rw [hR]

/-! ### MAR witness with a covariate-dependent response probability -/

/-- The response event `X = true ∨ ω.2 = true`, with covariate `X = ω.1`: everyone responds when
`X = true`, half the units when `X = false`. -/
def resp₂ : Set (Bool × Bool) := {ω | ω.1 = true ∨ ω.2 = true}

/-- **Non-vacuity of MAR**: any response event is conditionally independent, given `X`, of an
outcome that is a function of `X`. -/
theorem mar_comp {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] (μ : Measure Ω)
    (R : Set Ω) (X : Ω → β) (g : β → γ) :
    CondIndepDiscrete μ R (fun ω => g (X ω)) X := by
  intro B _ x
  by_cases hx : g x ∈ B
  · have h1 : (fun ω => g (X ω)) ⁻¹' B ∩ X ⁻¹' {x} = X ⁻¹' {x} :=
      Set.inter_eq_right.2 fun ω hω => by simpa [show X ω = x from hω] using hx
    rw [Set.inter_assoc, h1]
  · have h1 : (fun ω => g (X ω)) ⁻¹' B ∩ X ⁻¹' {x} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun ω hω => hx (by
        simpa [show X ω = x from hω.2] using hω.1)
    rw [Set.inter_assoc, h1]
    simp

/-- Positivity on the witness: each stratum contains the responding point `(x, true)`. -/
lemma propensity_resp₂_pos (x : Bool) : 0 < propensity coins resp₂ Prod.fst x := by
  have hsub : ({(x, true)} : Set (Bool × Bool)) ⊆ resp₂ ∩ Prod.fst ⁻¹' {x} := by
    simp [resp₂]
  have hnum : 0 < coins.real (resp₂ ∩ Prod.fst ⁻¹' {x}) :=
    (by rw [coins_real_singleton]; norm_num : (0 : ℝ) < coins.real {(x, true)}).trans_le
      (measureReal_mono hsub)
  exact div_pos hnum (hnum.trans_le (measureReal_mono Set.inter_subset_right))

/-- In the stratum `X = true` everyone responds: the response probability is `1`, allowed by
positivity (an overlap condition `π < 1` would exclude this witness). -/
example : propensity coins resp₂ Prod.fst true = 1 := by
  have h : resp₂ ∩ Prod.fst ⁻¹' {true} = Prod.fst ⁻¹' {true} := by
    ext ⟨a, b⟩; cases a <;> simp [resp₂]
  rw [propensity, h, div_self]
  rw [show (Prod.fst ⁻¹' {true} : Set (Bool × Bool)) = {true} ×ˢ Set.univ by ext; simp,
    coins_real_prod, coin_singleton, coin_real_univ]
  norm_num

/-- IPW identification on the MAR witness, outcome `Y = g X`. -/
example (g : Bool → ℝ) :
    ipwMean coins resp₂ Prod.fst (fun ω => g ω.1) = ∫ ω, g ω.1 ∂coins :=
  ipwMean_eq_integral_of_mar
    ((measurableSet_singleton true).preimage measurable_fst |>.union
      ((measurableSet_singleton true).preimage measurable_snd))
    measurable_fst (measurable_of_finite _) Integrable.of_finite
    (mar_comp coins resp₂ Prod.fst g) fun x _ => propensity_resp₂_pos x

/-! ### Boundaries -/

/-- **No respondents**: with `R = ∅`, MCAR holds vacuously but `P(R) = 0`, and the complete-case
mean is the junk value `0`, not `E[Y] = 1`. -/
example : completeCaseMean coins ∅ (fun _ => 1) = 0 ∧ ∫ _, (1 : ℝ) ∂coins = 1 := by
  refine ⟨completeCaseMean_of_measureReal_eq_zero _ (by simp), ?_⟩
  simp

/-- **Positivity failure**: with `R = ∅` the outcome is MAR given any covariate, positivity fails,
and the IPW mean is `0`, not `E[Y] = 1`. -/
example : CondIndepDiscrete coins ∅ (fun _ => (1 : ℝ)) Prod.fst ∧
    ipwMean coins ∅ Prod.fst (fun _ => 1) = 0 ∧ ∫ _, (1 : ℝ) ∂coins = 1 := by
  refine ⟨fun B _ x => by simp, by simp [ipwMean], by simp⟩

end MathlibExtTest.Probability.Causality.MissingData
