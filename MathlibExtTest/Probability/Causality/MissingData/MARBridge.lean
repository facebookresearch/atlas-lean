/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.MissingData.MARBridge
public import MathlibExtTest.Probability.Causality.MissingData.Definitions

/-!
# Tests for the bridge from MAR to mean MAR

The sample space is two fair coins, `Ω = Bool × Bool` (`coins`, from the `Definitions` tests),
with the response `R = heads₁` (the first coin shows heads).

* MAR without MCAR (`mar_fst`: the covariate is the first coin, the outcome the second): the
  product rule, mean MAR for every transform of the outcome, and mean MAR for the real outcome
  `coinY` (the hypothesis of the general inverse-weighting theorem), also through the
  general-σ-algebra form and from the discrete condition `CondIndepDiscrete`.
* MCAR with a constant covariate: response positivity `P(R | σ(X)) = 1/2` holds, so the inverse
  weighting corollary fires; both sides equal `E[coinY] = 1/2`.
* Strictness of the single-outcome form: for the outcome `Ycx = 1, -1, 0, 0` (on `(T,T)`, `(T,F)`,
  `(F,T)`, `(F,F)`) and a constant covariate, mean MAR holds for `Ycx` itself, yet MAR fails. So
  `missingAtRandomCondIndepFun_iff_forall_condExp` needs every transform `g ∘ Y`, not only `Y`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Causality.MissingData

namespace MathlibExtTest.Probability.Causality.MissingData

/-- The `0/1` coding of a coin. -/
noncomputable def coinCode : Bool → ℝ := fun b => if b then 1 else 0

/-- The second coin as a real outcome. -/
noncomputable def coinY : Bool × Bool → ℝ := coinCode ∘ Prod.snd

lemma measurable_coinY : Measurable coinY := .of_discrete

lemma coins_singleton (ω : Bool × Bool) : coins.real {ω} = 1 / 4 := by
  rw [show ({ω} : Set (Bool × Bool)) = {ω.1} ×ˢ {ω.2} by ext; simp [Prod.ext_iff],
    coins_prod, coin_singleton, coin_singleton]
  norm_num

lemma integral_coinY : ∫ ω, coinY ω ∂coins = 1 / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp [coins_singleton, coinY, coinCode, Fintype.sum_prod_type]
  norm_num

/-! ### MAR without MCAR -/

/-- MAR for the real outcome `coinY`, transported from `mar_fst` along the coding. -/
lemma mar_fst_coinY : MissingAtRandomCondIndepFun coins heads₁ Prod.fst measurable_fst coinY :=
  CondIndepFun.comp (φ := id) (ψ := coinCode) mar_fst measurable_id .of_discrete

/-- The product rule for a function of the conditioning variable and an arbitrary outcome. -/
example : coins[(coinCode ∘ Prod.fst) * coinY | MeasurableSpace.comap Prod.fst inferInstance]
    =ᵐ[coins] coins[coinCode ∘ Prod.fst | MeasurableSpace.comap Prod.fst inferInstance] *
      coins[coinY | MeasurableSpace.comap Prod.fst inferInstance] :=
  condExp_mul_of_condIndepFun measurable_fst.comap_le .of_discrete measurable_coinY
    (condIndepFun_of_measurable_left ((Measurable.of_discrete).comp (comap_measurable _))
      measurable_coinY)
    Integrable.of_finite Integrable.of_finite Integrable.of_finite

/-- Mean MAR for every transform `g` of the Boolean outcome. -/
example (g : Bool → ℝ) :
    coins[heads₁.indicator (g ∘ Prod.snd) | MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[coins] fun ω =>
        coins[heads₁.indicator 1 | MeasurableSpace.comap Prod.fst inferInstance] ω *
          coins[g ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] ω :=
  mar_fst.condExp_indicator_comp measurableSet_heads₁ measurable_snd .of_discrete
    Integrable.of_finite

/-- Mean MAR for the real outcome: the hypothesis of `integral_ipw_treated_condExp`. -/
example : coins[heads₁.indicator coinY | MeasurableSpace.comap Prod.fst inferInstance]
    =ᵐ[coins] fun ω =>
      coins[heads₁.indicator 1 | MeasurableSpace.comap Prod.fst inferInstance] ω *
        coins[coinY | MeasurableSpace.comap Prod.fst inferInstance] ω :=
  mar_fst_coinY.condExp_indicator_mul measurableSet_heads₁ measurable_coinY Integrable.of_finite

/-- The forward direction of the characterization, on the MAR witness. -/
example : ∀ g : Bool → ℝ, Measurable g → Integrable (g ∘ Prod.snd) coins →
    coins[heads₁.indicator (g ∘ Prod.snd) | MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[coins] fun ω =>
        coins[heads₁.indicator 1 | MeasurableSpace.comap Prod.fst inferInstance] ω *
          coins[g ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] ω :=
  (missingAtRandomCondIndepFun_iff_forall_condExp measurable_fst measurableSet_heads₁
    measurable_snd).1 mar_fst

/-- The general-σ-algebra form, applied to `m = σ(X)` directly. -/
example : coins[heads₁.indicator coinY | MeasurableSpace.comap Prod.fst inferInstance]
    =ᵐ[coins] fun ω =>
      coins[heads₁.indicator 1 | MeasurableSpace.comap Prod.fst inferInstance] ω *
        coins[coinY | MeasurableSpace.comap Prod.fst inferInstance] ω :=
  condExp_indicator_comp_of_condIndepFun measurable_fst.comap_le mar_fst_coinY
    measurableSet_heads₁ measurable_coinY measurable_id Integrable.of_finite

/-- Discrete MAR (`condIndepDiscrete_fst`, transported to the real coding) gives the mean form. -/
example : coins[heads₁.indicator coinY | MeasurableSpace.comap Prod.fst inferInstance]
    =ᵐ[coins] fun ω =>
      coins[heads₁.indicator 1 | MeasurableSpace.comap Prod.fst inferInstance] ω *
        coins[coinY | MeasurableSpace.comap Prod.fst inferInstance] ω :=
  condExp_indicator_mul_of_condIndepDiscrete
    (fun B _ w => condIndepDiscrete_fst (coinCode ⁻¹' B) .of_discrete w)
    measurableSet_heads₁ measurable_fst measurable_coinY Integrable.of_finite

/-! ### Inverse weighting under MCAR with a constant covariate -/

/-- MAR for `coinY` given a constant covariate, from the MCAR witness. -/
lemma mar_const_coinY :
    MissingAtRandomCondIndepFun coins heads₁ (fun _ => ()) measurable_const coinY :=
  CondIndepFun.comp (φ := id) (ψ := coinCode)
    (mcar_coins.missingAtRandomCondIndepFun measurableSet_heads₁ measurable_const measurable_snd)
    measurable_id .of_discrete

lemma const_preimage_unit : (fun _ : Bool × Bool => ()) ⁻¹' {()} = Set.univ :=
  Set.eq_univ_of_forall fun _ => rfl

/-- Response positivity: given a constant covariate, `P(R | σ(X)) = 1/2` almost everywhere. -/
lemma response_prob_const : ∀ᵐ ω ∂coins, (1 / 2 : ℝ) ≤
    coins[heads₁.indicator 1 | MeasurableSpace.comap (fun _ => ()) inferInstance] ω := by
  filter_upwards [condExp_indicator_comap_ae_eq (μ := coins) (measurable_const (a := ()))
    measurableSet_heads₁] with ω hω
  rw [show heads₁.indicator (1 : Bool × Bool → ℝ) = heads₁.indicator (fun _ => 1) from rfl, hω,
    propensity, const_preimage_unit, Set.inter_univ, coins_heads₁, probReal_univ]
  norm_num

/-- **The inverse-weighting corollary fires**, and both sides equal `E[coinY] = 1/2`. -/
example : ∫ ω, heads₁.indicator (fun ω => coinY ω /
      coins[heads₁.indicator 1 | MeasurableSpace.comap (fun _ => ()) inferInstance] ω) ω ∂coins =
    1 / 2 := by
  rw [mar_const_coinY.integral_ipw_eq_integral measurableSet_heads₁ measurable_coinY
    Integrable.of_finite (by norm_num) response_prob_const, integral_coinY]

/-! ### Mean MAR for the outcome alone is strictly weaker than MAR -/

/-- The outcome `1, -1` on the respondents and `0` on the nonrespondents. -/
noncomputable def Ycx : Bool × Bool → ℝ := fun ω => if ω.1 then (if ω.2 then 1 else -1) else 0

lemma integral_Ycx : ∫ ω, Ycx ω ∂coins = 0 := by
  rw [integral_fintype Integrable.of_finite]
  simp [coins_singleton, Ycx, Fintype.sum_prod_type]

/-- Mean MAR holds for `Ycx` given a constant covariate: both sides are `0`. -/
theorem meanMAR_Ycx :
    coins[heads₁.indicator Ycx | MeasurableSpace.comap (fun _ => ()) inferInstance] =ᵐ[coins]
      fun ω => coins[heads₁.indicator 1 | MeasurableSpace.comap (fun _ => ()) inferInstance] ω *
        coins[Ycx | MeasurableSpace.comap (fun _ => ()) inferInstance] ω := by
  have hR : heads₁.indicator Ycx = Ycx := by
    funext ω; by_cases h : ω.1 <;> simp [heads₁, Ycx, h]
  refine ae_of_all _ fun ω => ?_
  simp only [MeasurableSpace.comap_const, condExp_bot, hR, integral_Ycx, mul_zero]

/-- **MAR fails** for `Ycx`: `P(R, Ycx = 0) = 0` while `P(R) P(Ycx = 0) = 1/4`. -/
theorem not_mar_Ycx :
    ¬MissingAtRandomCondIndepFun coins heads₁ (fun _ => ()) measurable_const Ycx := by
  rw [missingAtRandomCondIndepFun_iff_condIndepDiscrete measurableSet_heads₁ measurable_const
    .of_discrete]
  intro h
  have key := h {0} (measurableSet_singleton 0) ()
  have h0 : heads₁ ∩ Ycx ⁻¹' {0} = ∅ := by
    ext ω; by_cases h1 : ω.1 <;> by_cases h2 : ω.2 <;> simp [heads₁, Ycx, h1, h2]
  have h1 : Ycx ⁻¹' {0} = {false} ×ˢ Set.univ := by
    ext ω; by_cases h1 : ω.1 <;> by_cases h2 : ω.2 <;> simp [Ycx, h1, h2]
  rw [const_preimage_unit, Set.inter_univ, Set.inter_univ, Set.inter_univ, h0, h1,
    coins_prod, coins_heads₁, coin_singleton, coin_univ] at key
  norm_num at key

/-- The single-outcome mean form does not imply MAR. -/
example : ¬((coins[heads₁.indicator Ycx | MeasurableSpace.comap (fun _ => ()) inferInstance]
      =ᵐ[coins] fun ω =>
        coins[heads₁.indicator 1 | MeasurableSpace.comap (fun _ => ()) inferInstance] ω *
          coins[Ycx | MeasurableSpace.comap (fun _ => ()) inferInstance] ω) →
    MissingAtRandomCondIndepFun coins heads₁ (fun _ => ()) measurable_const Ycx) :=
  fun h => not_mar_Ycx (h meanMAR_Ycx)

end MathlibExtTest.Probability.Causality.MissingData
