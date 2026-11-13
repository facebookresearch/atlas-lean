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
# Tests for the product rule and the characterization of MAR by mean MAR

The sample space is two fair coins, `Ω = Bool × Bool` (`coins`, from the `Definitions` tests),
with the response `R = heads₁` (the first coin shows heads).

* The product rule, for a function of the covariate (the first coin) and the second coin.
* The forward direction of `missingAtRandomCondIndepFun_iff_forall_condExp` on the MAR witness
  `mar_fst` (the covariate is the first coin, the outcome the second).
* The converse in general: set-wise MAR given `σ(X)` gives mean MAR for every transform of the
  outcome (`condExp_indicator_ae_eq_mul_of_mar`), so the converse turns it into MAR.
* The converse fires on the coins: given a constant covariate, mean MAR for every transform `g` of
  the second coin is computed from the definitions, and the converse turns it into MAR.
* Strictness of the single-outcome form: for the outcome `Ycx = 1, -1, 0, 0` (on `(T,T)`, `(T,F)`,
  `(F,T)`, `(F,F)`) and a constant covariate, mean MAR holds for `Ycx` itself, yet MAR fails. So
  the characterization needs every transform `g ∘ Y`, not only `Y`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Causality.MissingData

namespace MathlibExtTest.Probability.Causality.MissingData.MARBridge

/-- The `0/1` coding of a coin. -/
noncomputable def coinCode : Bool → ℝ := fun b => if b then 1 else 0

/-- The second coin as a real outcome. -/
noncomputable def coinSnd : Bool × Bool → ℝ := coinCode ∘ Prod.snd

lemma measurable_coinSnd : Measurable coinSnd := .of_discrete

lemma coins_singleton (ω : Bool × Bool) : coins.real {ω} = 1 / 4 := by
  rw [show ({ω} : Set (Bool × Bool)) = {ω.1} ×ˢ {ω.2} by ext; simp [Prod.ext_iff],
    coins_prod, coin_singleton, coin_singleton]
  norm_num

lemma const_preimage_unit : (fun _ : Bool × Bool => ()) ⁻¹' {()} = Set.univ :=
  Set.eq_univ_of_forall fun _ => rfl

/-! ### The product rule -/

/-- The product rule for a function of the conditioning variable and an arbitrary outcome. -/
example : coins[(coinCode ∘ Prod.fst) * coinSnd | MeasurableSpace.comap Prod.fst inferInstance]
    =ᵐ[coins] coins[coinCode ∘ Prod.fst | MeasurableSpace.comap Prod.fst inferInstance] *
      coins[coinSnd | MeasurableSpace.comap Prod.fst inferInstance] :=
  condExp_mul_of_condIndepFun measurable_fst.comap_le .of_discrete measurable_coinSnd
    (condIndepFun_of_measurable_left ((Measurable.of_discrete).comp (comap_measurable _))
      measurable_coinSnd)
    Integrable.of_finite Integrable.of_finite Integrable.of_finite

/-! ### MAR is mean MAR for every transform of the outcome -/

/-- The forward direction of the characterization, on the MAR witness. -/
example : ∀ g : Bool → ℝ, Measurable g → Integrable (g ∘ Prod.snd) coins →
    coins[heads₁.indicator (g ∘ Prod.snd) | MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[coins] fun ω =>
        coins[heads₁.indicator 1 | MeasurableSpace.comap Prod.fst inferInstance] ω *
          coins[g ∘ Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] ω :=
  (missingAtRandomCondIndepFun_iff_forall_condExp measurable_fst measurableSet_heads₁
    measurable_snd).1 mar_fst

/-- **Set-wise MAR given `σ(X)` implies MAR**, through the converse: set-wise MAR for `Y` gives
mean MAR for every transform `g ∘ Y` by `condExp_indicator_ae_eq_mul_of_mar`. -/
example {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] [m𝒳 : MeasurableSpace 𝒳] [MeasurableSpace 𝒴] {R : Set Ω}
    (hR : MeasurableSet R) {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → 𝒴} (hY : Measurable Y)
    (hMAR : ∀ t, MeasurableSet t →
      (μ⟦R ∩ Y ⁻¹' t | m𝒳.comap X⟧) =ᵐ[μ] (μ⟦R | m𝒳.comap X⟧) * (μ⟦Y ⁻¹' t | m𝒳.comap X⟧)) :
    MissingAtRandomCondIndepFun μ R X hX Y :=
  (missingAtRandomCondIndepFun_iff_forall_condExp hX hR hY).2 fun g hg hgY =>
    condExp_indicator_ae_eq_mul_of_mar hX.comap_le hR (hg.comp hY) hgY
      fun S hS => hMAR (g ⁻¹' S) (hg hS)

/-- **The converse fires.** Given a constant covariate, conditional expectations are means, and
mean MAR for every transform `g` of the second coin is computed from the definitions: both sides
equal `(g true + g false) / 4`. The converse turns this into MAR. -/
theorem mar_const_of_forall_condExp :
    MissingAtRandomCondIndepFun coins heads₁ (fun _ => ()) measurable_const Prod.snd := by
  refine (missingAtRandomCondIndepFun_iff_forall_condExp measurable_const measurableSet_heads₁
    measurable_snd).2 fun g _ _ => ae_of_all _ fun ω => ?_
  simp only [MeasurableSpace.comap_const, condExp_bot]
  rw [integral_fintype Integrable.of_finite, integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite]
  simp [coins_singleton, heads₁, Fintype.sum_prod_type]
  ring

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

end MathlibExtTest.Probability.Causality.MissingData.MARBridge
