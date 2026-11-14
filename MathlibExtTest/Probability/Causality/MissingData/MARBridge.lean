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
* Which `hMAR` each form discharges: the set-wise form is the hypothesis of
  `integral_ipw_eq_integral_of_mar_sigma` (`GeneralIPW`), the mean form that of
  `integral_ipw_eq_integral_of_mar_condExp` (`Identification`); `MissingAtRandomCondIndepFun`
  reaches the latter through the former.
* Discrete MAR without standard Borel: `Latent` has a covariate, an outcome and a latent coin the
  σ-algebra does not see, so its singletons are not measurable and it is not standard Borel
  (`not_standardBorelSpace_latent`). With response `R = {X = true}`, `CondIndepDiscrete` holds for
  every measure and every outcome, checked by set algebra from the definition, and the discrete
  theorems give the set-wise and mean forms.
* Where the route does not apply: on `Latent`, the self-masking response `R = {Y = true}` under
  `mnarLaw` (two points with `X = true` and `Y = true, false`) fails `CondIndepDiscrete`, and the
  set-wise form fails too: `P(R ∩ {Y = true} | σ(X)) = 1/2` while
  `P(R | σ(X)) P(Y = true | σ(X)) = 1/4`. Both are computed from the definitions; no MAR
  conclusion is claimed there.
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

/-! ### Which `hMAR` each form discharges -/

/-- The set-wise form from discrete MAR is the hypothesis of `integral_ipw_eq_integral_of_mar_sigma`
(`GeneralIPW`), with no standard Borel assumption. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [m𝒳 : MeasurableSpace 𝒳] [Countable 𝒳] [MeasurableSingletonClass 𝒳] {R : Set Ω}
    {X : Ω → 𝒳} {Y : Ω → ℝ} (h : CondIndepDiscrete μ R Y X) (hR : MeasurableSet R)
    (hX : Measurable X) (hY : Measurable Y) (hYi : Integrable Y μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ (μ⟦R | m𝒳.comap X⟧) ω) :
    ∫ ω, R.indicator (fun ω => Y ω / (μ⟦R | m𝒳.comap X⟧) ω) ω ∂μ = ∫ ω, Y ω ∂μ :=
  integral_ipw_eq_integral_of_mar_sigma hX.comap_le hR hY hYi
    (condExp_inter_preimage_ae_eq_mul_of_condIndepDiscrete h hR hX hY) hε hpos

/-- The mean form from discrete MAR is the hypothesis of `integral_ipw_eq_integral_of_mar_condExp`
(`Identification`), with no standard Borel assumption. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [m𝒳 : MeasurableSpace 𝒳] [Countable 𝒳] [MeasurableSingletonClass 𝒳] {R : Set Ω}
    {X : Ω → 𝒳} {Y : Ω → ℝ} (h : CondIndepDiscrete μ R Y X) (hR : MeasurableSet R)
    (hX : Measurable X) (hY : Measurable Y) (hYi : Integrable Y μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ μ[R.indicator 1 | m𝒳.comap X] ω) :
    ∫ ω, R.indicator (fun ω => Y ω / μ[R.indicator 1 | m𝒳.comap X] ω) ω ∂μ = ∫ ω, Y ω ∂μ :=
  integral_ipw_eq_integral_of_mar_condExp hX.comap_le hR hYi
    (condExp_indicator_mul_of_condIndepDiscrete h hR hX hY hYi) hε hpos

/-- `MissingAtRandomCondIndepFun` discharges `Identification`'s mean-form `hMAR` through the
set-wise form: `condExp_inter_preimage_ae_eq_mul_of_condIndepFun`, then
`condExp_indicator_ae_eq_mul_of_mar`. -/
example {Ω 𝒳 : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [m𝒳 : MeasurableSpace 𝒳] {R : Set Ω} {X : Ω → 𝒳}
    (hX : Measurable X) {Y : Ω → ℝ} (h : MissingAtRandomCondIndepFun μ R X hX Y)
    (hR : MeasurableSet R) (hY : Measurable Y) (hYi : Integrable Y μ) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ μ[R.indicator 1 | m𝒳.comap X] ω) :
    ∫ ω, R.indicator (fun ω => Y ω / μ[R.indicator 1 | m𝒳.comap X] ω) ω ∂μ = ∫ ω, Y ω ∂μ :=
  integral_ipw_eq_integral_of_mar_condExp hX.comap_le hR hYi
    (condExp_indicator_ae_eq_mul_of_mar hX.comap_le hR hY hYi
      (condExp_inter_preimage_ae_eq_mul_of_condIndepFun hX.comap_le hR hY h)) hε hpos

/-! ### Discrete MAR on a sample space that is not standard Borel -/

/-- A unit with a covariate `x`, an outcome `y` and a latent coin `u`. -/
structure Latent where
  /-- The covariate. -/
  x : Bool
  /-- The outcome. -/
  y : Bool
  /-- A latent coin that the σ-algebra does not see. -/
  u : Bool

/-- The observed coordinates `(x, y)`. -/
def Latent.obs (ω : Latent) : Bool × Bool := (ω.x, ω.y)

/-- Events are the events of the observed coordinates; the latent coin is not measurable. -/
instance : MeasurableSpace Latent := MeasurableSpace.comap Latent.obs inferInstance

lemma measurable_latentObs : Measurable Latent.obs := comap_measurable _

/-- The covariate. -/
def latX : Latent → Bool := Latent.x

/-- The outcome. -/
def latY : Latent → Bool := Latent.y

lemma measurable_latX : Measurable latX := measurable_fst.comp measurable_latentObs

lemma measurable_latY : Measurable latY := measurable_snd.comp measurable_latentObs

/-- No singleton of `Latent` is measurable: an event cannot separate the two values of the
latent coin. -/
theorem not_measurableSet_singleton_latent (a : Latent) : ¬MeasurableSet ({a} : Set Latent) := by
  intro h
  obtain ⟨T, -, hT⟩ := MeasurableSpace.measurableSet_comap.1 h
  have ha : a ∈ Latent.obs ⁻¹' T := (Set.ext_iff.1 hT a).2 rfl
  have hb : (⟨a.x, a.y, !a.u⟩ : Latent) ∈ Latent.obs ⁻¹' T := ha
  have hu := congrArg Latent.u (Set.mem_singleton_iff.1 ((Set.ext_iff.1 hT _).1 hb))
  cases a with
  | mk x y u => cases u <;> simp at hu

/-- **`Latent` is not standard Borel**: a standard Borel space has measurable singletons. -/
theorem not_standardBorelSpace_latent : ¬StandardBorelSpace Latent := by
  intro _
  exact not_measurableSet_singleton_latent ⟨true, true, true⟩ (measurableSet_singleton _)

/-- The response depends on the covariate only: `R = {X = true}`. -/
def latR : Set Latent := latX ⁻¹' {true}

lemma measurableSet_latR : MeasurableSet latR := measurable_latX (measurableSet_singleton true)

/-- **Discrete MAR on `Latent`**, for every measure and every outcome, from the definition of
`CondIndepDiscrete`: `R ∩ {X = x}` is `∅` for `x = false` and `{X = x}` for `x = true`. -/
theorem condIndepDiscrete_latR {β : Type*} [MeasurableSpace β] (μ : Measure Latent)
    (V : Latent → β) : CondIndepDiscrete μ latR V latX := by
  intro B _ x
  rw [Set.inter_right_comm]
  cases x
  · have h0 : latR ∩ latX ⁻¹' {false} = ∅ := by
      ext ω
      simp only [latR, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h
      simp [h]
    rw [h0, Set.empty_inter, measureReal_empty, zero_mul, zero_mul]
  · have h1 : latR ∩ latX ⁻¹' {true} = latX ⁻¹' {true} := Set.inter_self _
    rw [h1, Set.inter_comm (latX ⁻¹' {true}), mul_comm]

/-- **Set-wise MAR on a sample space that is not standard Borel**, for every finite measure on
`Latent`. -/
example (μ : Measure Latent) [IsFiniteMeasure μ] :
    ∀ S, MeasurableSet S →
      (μ⟦latR ∩ latY ⁻¹' S | MeasurableSpace.comap latX inferInstance⟧) =ᵐ[μ]
        (μ⟦latR | MeasurableSpace.comap latX inferInstance⟧) *
          (μ⟦latY ⁻¹' S | MeasurableSpace.comap latX inferInstance⟧) :=
  condExp_inter_preimage_ae_eq_mul_of_condIndepDiscrete (condIndepDiscrete_latR μ latY)
    measurableSet_latR measurable_latX measurable_latY

/-- The outcome of `Latent` coded `0/1`. -/
noncomputable def latYr : Latent → ℝ := coinCode ∘ latY

lemma measurable_latYr : Measurable latYr := (Measurable.of_discrete).comp measurable_latY

/-- **Mean MAR on a sample space that is not standard Borel**, for every finite measure on
`Latent`: the mean-form `hMAR` of `integral_ipw_eq_integral_of_mar_condExp`. -/
example (μ : Measure Latent) [IsFiniteMeasure μ] :
    μ[latR.indicator latYr | MeasurableSpace.comap latX inferInstance] =ᵐ[μ] fun ω =>
      μ[latR.indicator 1 | MeasurableSpace.comap latX inferInstance] ω *
        μ[latYr | MeasurableSpace.comap latX inferInstance] ω :=
  condExp_indicator_mul_of_condIndepDiscrete (condIndepDiscrete_latR μ latYr) measurableSet_latR
    measurable_latX measurable_latYr
    (Integrable.of_bound measurable_latYr.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      by_cases h : latY ω <;> simp [latYr, coinCode, h]))

/-! ### Where the set-wise route does not apply -/

/-- Two units with covariate `true`, outcomes `true` and `false`. -/
noncomputable def mnarLaw : Measure Latent :=
  Measure.dirac ⟨true, true, false⟩ + Measure.dirac ⟨true, false, false⟩

instance : IsFiniteMeasure mnarLaw := by unfold mnarLaw; infer_instance

/-- The self-masking response `R = {Y = true}`: missing not at random. -/
def latRm : Set Latent := latY ⁻¹' {true}

lemma measurableSet_latRm : MeasurableSet latRm := measurable_latY (measurableSet_singleton true)

open Classical in
lemma mnarLaw_real {s : Set Latent} (hs : MeasurableSet s) :
    mnarLaw.real s = (if (⟨true, true, false⟩ : Latent) ∈ s then 1 else 0) +
      (if (⟨true, false, false⟩ : Latent) ∈ s then 1 else 0) := by
  rw [mnarLaw, measureReal_def, Measure.add_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs]
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs <;> norm_num [ENNReal.toReal_add]

lemma mnarLaw_X_true : mnarLaw.real (latX ⁻¹' {true}) = 2 := by
  rw [mnarLaw_real (measurable_latX (measurableSet_singleton true))]
  norm_num [latX]

/-- **Discrete MAR fails** under `mnarLaw` for the self-masking response: at `B = {true}`,
`x = true`, the two sides of `CondIndepDiscrete` are `1 · 2` and `1 · 1`. -/
theorem not_condIndepDiscrete_latRm : ¬CondIndepDiscrete mnarLaw latRm latY latX := by
  intro h
  have key := h {true} (measurableSet_singleton true) true
  have hXt := measurable_latX (measurableSet_singleton true)
  have hYt := measurable_latY (measurableSet_singleton true)
  rw [mnarLaw_real ((measurableSet_latRm.inter hYt).inter hXt), mnarLaw_X_true,
    mnarLaw_real (measurableSet_latRm.inter hXt), mnarLaw_real (hYt.inter hXt)] at key
  norm_num [latRm, latX, latY] at key

/-- **The set-wise form fails** under `mnarLaw` for the self-masking response, at `S = {true}`:
given `σ(X)` (here `X = true` almost surely), `P(R ∩ {Y = true} | σ(X)) = 1/2` and
`P(R | σ(X)) P(Y = true | σ(X)) = 1/2 · 1/2`. Each conditional probability is computed as a
propensity by `condExp_indicator_comap_ae_eq`. So no MAR conclusion holds here. -/
theorem not_setwise_latRm :
    ¬∀ S, MeasurableSet S →
      (mnarLaw⟦latRm ∩ latY ⁻¹' S | MeasurableSpace.comap latX inferInstance⟧) =ᵐ[mnarLaw]
        (mnarLaw⟦latRm | MeasurableSpace.comap latX inferInstance⟧) *
          (mnarLaw⟦latY ⁻¹' S | MeasurableSpace.comap latX inferInstance⟧) := by
  intro H
  have hXt := measurable_latX (measurableSet_singleton true)
  have hYt := measurable_latY (measurableSet_singleton true)
  have hRY := measurableSet_latRm.inter hYt
  have hXae : ∀ᵐ ω ∂mnarLaw, latX ω = true := by
    have hc : MeasurableSet {ω | ¬latX ω = true} := hXt.compl
    refine ae_iff.2 ((measureReal_eq_zero_iff).1 ?_)
    rw [mnarLaw_real hc]
    norm_num [latX]
  have hne : mnarLaw ≠ 0 := fun h0 => by
    have h2 := mnarLaw_X_true
    rw [h0] at h2
    norm_num at h2
  have hfalse : ∀ᵐ _ ∂mnarLaw, False := by
    filter_upwards [H {true} (measurableSet_singleton true),
      condExp_indicator_comap_ae_eq (μ := mnarLaw) measurable_latX hRY,
      condExp_indicator_comap_ae_eq (μ := mnarLaw) measurable_latX measurableSet_latRm,
      condExp_indicator_comap_ae_eq (μ := mnarLaw) measurable_latX hYt, hXae]
      with ω h0 h1 h2 h3 hω
    rw [Pi.mul_apply, h1, h2, h3, hω] at h0
    simp only [propensity] at h0
    rw [mnarLaw_real (hRY.inter hXt), mnarLaw_real (measurableSet_latRm.inter hXt),
      mnarLaw_real (hYt.inter hXt), mnarLaw_X_true] at h0
    norm_num [latRm, latX, latY] at h0
  exact hne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse))

end MathlibExtTest.Probability.Causality.MissingData.MARBridge
