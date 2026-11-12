/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Identifiability
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Deterministic

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics
open MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Statistics.Identifiability

/-- Duplicate parameter labels with equal estimand values are allowed: a constant estimand is
identified by any family, including one that is not injective. -/
example : IsIdentifiedBy (fun _ : Bool => Measure.dirac (0 : ℝ)) (fun _ => (1 : ℝ)) := by
  exact fun _ _ _ => rfl

/-- Two indistinguishable laws with different latent means are not identified. -/
example : ¬ IsIdentifiedBy (fun _ : Bool => Measure.dirac (0 : ℝ))
    (fun b => if b then (1 : ℝ) else 0) := by
  exact not_isIdentifiedBy_of_eq_of_ne (θ := true) (θ' := false) rfl (by norm_num)

/-- Strict separation matters: at the boundary `2ε = |τ θ - τ θ'|` (`τ θ = 0`, `τ θ' = 2`,
`ε = 1`) the constant estimator `δ ≡ 1` succeeds at both parameters, so the success
probabilities sum to `2`. -/
example : (Measure.dirac (0 : ℝ)).real {x : ℝ | |(fun _ : ℝ => (1 : ℝ)) x - 0| ≤ 1} +
    (Measure.dirac (0 : ℝ)).real {x : ℝ | |(fun _ : ℝ => (1 : ℝ)) x - 2| ≤ 1} = 2 := by
  rw [Measure.dirac_real_apply_of_mem (by norm_num),
    Measure.dirac_real_apply_of_mem (by norm_num)]
  norm_num

/-- `ε = 0` is admitted: exact recovery fails with probability at least `1/2` at one of two
indistinguishable parameters with distinct estimand values. -/
example {δ : ℝ → ℝ} (hδ : Measurable δ) :
    1 / 2 ≤ (Measure.dirac (0 : ℝ)).real {x | 0 < |δ x - 0|} ∨
      1 / 2 ≤ (Measure.dirac (0 : ℝ)).real {x | 0 < |δ x - 1|} := by
  exact exists_measureReal_failure_ge_half (fun _ : Bool => Measure.dirac (0 : ℝ))
    (fun b => if b then (1 : ℝ) else 0) (θ := false) (θ' := true) rfl hδ le_rfl (by norm_num)

/-- A fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The sign `±1` of a coin toss. -/
noncomputable def coinSign (b : Bool) : ℝ := if b then 1 else -1

/-- Positive: two equal fair-coin laws with latent estimands `0` and `1` fire the bound at
`ε = 1 / 4`. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin
    let τ : Bool → ℝ := fun b => if b then 0 else 1
    1 / 2 ≤ (P true).real {x | (1 / 4 : ℝ) < |coinSign x - τ true|} ∨
      1 / 2 ≤ (P false).real {x | (1 / 4 : ℝ) < |coinSign x - τ false|} := by
  intro P τ
  have hP : P true = P false := rfl
  have hδ : Measurable coinSign := Measurable.of_discrete
  have hε : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsep : 2 * (1 / 4 : ℝ) < |τ true - τ false| := by
    show 2 * (1 / 4 : ℝ) < |(0 : ℝ) - 1|
    norm_num
  haveI hI : IsProbabilityMeasure (P true) := by
    show IsProbabilityMeasure fairCoin
    infer_instance
  exact MathlibExt.Probability.Statistics.exists_measureReal_failure_ge_half
    (δ := coinSign) (ε := 1 / 4) P τ hP hδ hε hsep

/-- Boundary: at `2ε = |Δτ|` the success sets overlap (`1 / 2` lies in both). -/
example : ¬ Disjoint ({x : ℝ | |x - (0 : ℝ)| ≤ 1 / 2} : Set ℝ)
    ({x : ℝ | |x - (1 : ℝ)| ≤ 1 / 2} : Set ℝ) := by
  have h1 : |(1 / 2 : ℝ) - 0| ≤ 1 / 2 := by norm_num
  have h2 : |(1 / 2 : ℝ) - 1| ≤ 1 / 2 := by norm_num
  intro h
  exact (Set.disjoint_left.mp h h1) h2

/-- Boundary: at `ε = 0` the success sets need not be disjoint. With equal estimands the
two `ε`-success sets coincide, so disjointness fails. -/
example : ¬ Disjoint ({x : ℝ | |x - (0 : ℝ)| ≤ (0 : ℝ)} : Set ℝ)
    ({x : ℝ | |x - (0 : ℝ)| ≤ (0 : ℝ)} : Set ℝ) := by
  have h0 : |(0 : ℝ) - 0| ≤ (0 : ℝ) := by simp
  intro h
  exact (Set.disjoint_left.mp h h0) h0

/-- Vacuity: with equal estimands the separation hypothesis is impossible. -/
example (τ : Bool → ℝ) (h : τ true = τ false) :
    ¬ ∃ ε : ℝ, 0 ≤ ε ∧ 2 * ε < |τ true - τ false| := by
  intro ⟨ε, hε, hsep⟩
  rw [h, sub_self, abs_zero] at hsep
  linarith

/-- Constant Gaussian kernel (randomized): every observation draws `N(0, 1)` independently
of the input. -/
noncomputable def gaussKernel : Kernel Bool ℝ :=
  Kernel.const Bool (gaussianReal (0 : ℝ) 1)

instance : IsMarkovKernel gaussKernel := by
  refine IsMarkovKernel.mk fun _ => ?_
  show IsProbabilityMeasure (gaussianReal (0 : ℝ) 1)
  exact inferInstance

/-- Randomized-kernel use: a constant Gaussian kernel fires the kernel bound. The
conclusion is the kernel theorem's disjunction verbatim; no output-law computation is
needed. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin;
    let τ : Bool → ℝ := fun b => if b then 0 else 1;
    1 / 2 ≤ ((P true).bind gaussKernel).real {y | (1 / 4 : ℝ) < |y - τ true|} ∨
      1 / 2 ≤ ((P false).bind gaussKernel).real {y | (1 / 4 : ℝ) < |y - τ false|} := by
  intro P τ
  have hP : P true = P false := rfl
  have hI : IsProbabilityMeasure (P true) := by
    show IsProbabilityMeasure fairCoin
    exact inferInstance
  have hε : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsep : 2 * (1 / 4 : ℝ) < |τ true - τ false| := by
    show 2 * (1 / 4 : ℝ) < |(0 : ℝ) - 1|
    norm_num
  exact MathlibExt.Probability.Statistics.exists_measureReal_failure_ge_half_kernel
    P τ hP hε hsep

/-- Deterministic-kernel use: `Kernel.deterministic` recovers the deterministic bound as a
corollary of the kernel bound. -/
example :
    let P : Bool → Measure Bool := fun _ => fairCoin;
    let τ : Bool → ℝ := fun b => if b then 0 else 1;
    1 / 2 ≤ ((P true).bind (Kernel.deterministic coinSign Measurable.of_discrete)).real
        {y | (1 / 4 : ℝ) < |y - τ true|} ∨
      1 / 2 ≤ ((P false).bind (Kernel.deterministic coinSign Measurable.of_discrete)).real
        {y | (1 / 4 : ℝ) < |y - τ false|} := by
  intro P τ
  have hP : P true = P false := rfl
  have hδ : Measurable coinSign := Measurable.of_discrete
  have hI : IsProbabilityMeasure (P true) := by
    show IsProbabilityMeasure fairCoin
    exact inferInstance
  have hε : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hsep : 2 * (1 / 4 : ℝ) < |τ true - τ false| := by
    show 2 * (1 / 4 : ℝ) < |(0 : ℝ) - 1|
    norm_num
  exact MathlibExt.Probability.Statistics.exists_measureReal_failure_ge_half_of_deterministic
    P τ hP hδ hε hsep

/-- Negative: when the outcome drives treatment, conditional independence fails, so no
`StronglyIgnorable` hypothesis is available and the per-setting equation does not apply.
With two fair coins, `T = {fst}` and `V = fst` at `B = {true}`, `w = ()`: LHS `1/2`,
RHS `1/4`. -/
example : ¬ CondIndepDiscrete (fairCoin.prod fairCoin) {ω : Bool × Bool | ω.1 = true}
    (fun ω : Bool × Bool => ω.1) (fun _ : Bool × Bool => ()) := by
  intro h
  have hcon := h {true} (measurableSet_singleton true) ()
  have hT : {ω : Bool × Bool | ω.1 = true} = ({true} ×ˢ (Set.univ : Set Bool)) := by
    ext ⟨a, b⟩
    simp
  have hV : (fun ω : Bool × Bool => ω.1) ⁻¹' ({true} : Set Bool) =
      ({true} ×ˢ (Set.univ : Set Bool)) := by
    ext ⟨a, b⟩
    simp
  have hW : (fun _ : Bool × Bool => ()) ⁻¹' ({()} : Set Unit) = Set.univ := by
    ext ⟨a, b⟩
    simp
  rw [hT, hV, hW] at hcon
  simp only [Set.inter_self, Set.inter_univ] at hcon
  have hcoin : fairCoin {true} = (2 : ENNReal)⁻¹ := by simp [fairCoin]
  have hprod : (fairCoin.prod fairCoin) ({true} ×ˢ (Set.univ : Set Bool)) = (2 : ENNReal)⁻¹ := by
    rw [Measure.prod_prod, hcoin, measure_univ, mul_one]
  unfold Measure.real at hcon
  rw [hprod, measure_univ] at hcon
  norm_num at hcon

/-- Positive: ignorability passes through measurable transformations of the outcome. -/
example {Ω β γ δ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure Ω} {T : Set Ω} {V : Ω → β} {W : Ω → δ} {g : β → γ}
    (h : StronglyIgnorable μ T V W) (hg : Measurable g) :
    StronglyIgnorable μ T (g ∘ V) W := by
  exact h.comp hg

/-- Boundary: overlap gives strict propensity bounds at every positive-probability value. -/
example {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {μ : Measure Ω} {T : Set Ω} {V : Ω → β} {W : Ω → γ}
    (h : StronglyIgnorable μ T V W) (w : γ) (hw : μ (W ⁻¹' {w}) ≠ 0) :
    0 < propensity μ T W w ∧ propensity μ T W w < 1 := by
  exact h.2 w hw

/-- Positive: duplicate parameter labels with identical data are identified. Apply the
wrapper with constant families. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T)
    {𝒳 : Type*} [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hY₀i : Integrable Y₀ μ) (hY₁i : Integrable Y₁ μ)
    (hSI : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) X) :
    IsIdentifiedBy (fun _ : Bool => obsLaw μ T X Y₀ Y₁)
      (fun _ : Bool => ∫ ω, (Y₁ ω - Y₀ ω) ∂μ) := by
  exact ate_isIdentifiedBy_observational_law (μ := fun _ => μ) (T := fun _ => T) (X := fun _ => X)
    (Y₀ := fun _ => Y₀) (Y₁ := fun _ => Y₁) (fun _ => hT) (fun _ => hX) (fun _ => hY₀) (fun _ => hY₁)
    (fun _ => hY₀i) (fun _ => hY₁i) (fun _ => hSI)

/-- Two-coin observational model: the covariate reads the first coin, treatment is the
second coin, and the potential outcomes read the first coin. -/
private def obsT : Set (Bool × Bool) := {ω | ω.2 = true}
private def obsX : Bool × Bool → Bool := fun ω => ω.1
private def obsY0 : Bool × Bool → ℝ := fun ω => if ω.1 then 1 else 0
private def obsY1 : Bool × Bool → ℝ := fun ω => if ω.1 then 3 else 0

/-- Non-vacuous coverage: on the two-coin model the law-read propensity is `1 / 2` at both
covariate values and the law-read IPW functional equals `1`. Both `propensityFromLaw` and
`ipwATE` are evaluated on the pushed-forward observational law. -/
example :
    (∀ w : Bool, propensityFromLaw
      (obsLaw (fairCoin.prod fairCoin) obsT obsX obsY0 obsY1) w = 1 / 2) ∧
    ipwATE (obsLaw (fairCoin.prod fairCoin) obsT obsX obsY0 obsY1) = 1 := by
  classical
  have hT : MeasurableSet obsT := by
    unfold obsT
    exact measurable_snd (measurableSet_singleton true)
  have hX : Measurable obsX := by
    unfold obsX
    exact measurable_fst
  have hY0 : Measurable obsY0 := by
    unfold obsY0
    exact Measurable.of_discrete
  have hY1 : Measurable obsY1 := by
    unfold obsY1
    exact Measurable.of_discrete
  have hobsY : Measurable (observed obsT obsY0 obsY1) := by
    unfold observed
    exact (Measurable.indicator hY1 hT).add (Measurable.indicator hY0 hT.compl)
  have h1 : Measurable fun ω : Bool × Bool => obsT.indicator (1 : Bool × Bool → ℝ) ω :=
    Measurable.indicator measurable_const hT
  have hobs : Measurable (obsDatum obsT obsX obsY0 obsY1) := by
    unfold obsDatum
    exact hX.prodMk (h1.prodMk hobsY)
  have hdatum : ∀ ω : Bool × Bool, obsDatum obsT obsX obsY0 obsY1 ω
      = (obsX ω, obsT.indicator 1 ω, observed obsT obsY0 obsY1 ω) := fun ω => rfl
  have hXv : ∀ ω : Bool × Bool, obsX ω = ω.1 := fun ω => rfl
  have hY0v : ∀ ω : Bool × Bool, obsY0 ω = (if ω.1 then (1 : ℝ) else 0) := fun ω => rfl
  have hY1v : ∀ ω : Bool × Bool, obsY1 ω = (if ω.1 then (3 : ℝ) else 0) := fun ω => rfl
  have hind : ∀ ω : Bool × Bool, obsT.indicator (1 : Bool × Bool → ℝ) ω = 1 ↔ ω ∈ obsT := by
    intro ω
    by_cases hmem : ω ∈ obsT
    · rw [Set.indicator_of_mem hmem]; simp [hmem]
    · rw [Set.indicator_of_notMem hmem]; simp [hmem]
  have hmemT : ∀ ω : Bool × Bool, ω ∈ obsT ↔ ω.2 = true := fun ω => Iff.rfl
  have hcoin : ∀ b : Bool, fairCoin {b} = (2 : ENNReal)⁻¹ := by
    intro b
    cases b <;> simp [fairCoin]
  have hpre1 : ∀ w : Bool, (obsDatum obsT obsX obsY0 obsY1) ⁻¹'
      ({w} ×ˢ ({1} ×ˢ (Set.univ : Set ℝ)))
      = {w} ×ˢ ({true} : Set Bool) := by
    intro w
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, hdatum, hXv, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, and_true, hind, hmemT]
  have hpre2 : ∀ w : Bool, (obsDatum obsT obsX obsY0 obsY1) ⁻¹'
      ({w} ×ˢ (Set.univ ×ˢ (Set.univ : Set ℝ)))
      = {w} ×ˢ (Set.univ : Set Bool) := by
    intro w
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, hdatum, hXv, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, and_true]
  have hmuP : ∀ a b : Bool, ((fairCoin.prod fairCoin) ({a} ×ˢ ({b} : Set Bool))).toReal
      = 1 / 4 := by
    intro a b
    rw [Measure.prod_prod, hcoin a, hcoin b]
    norm_num [ENNReal.toReal_mul]
  have hmu2 : ∀ w : Bool, ((fairCoin.prod fairCoin) ({w} ×ˢ (Set.univ : Set Bool))).toReal
      = 1 / 2 := by
    intro w
    rw [Measure.prod_prod, hcoin w, measure_univ, mul_one]
    simp
  have hprop : ∀ w : Bool, propensityFromLaw
      (obsLaw (fairCoin.prod fairCoin) obsT obsX obsY0 obsY1) w = 1 / 2 := by
    intro w
    unfold propensityFromLaw obsLaw Measure.real
    rw [Measure.map_apply hobs ((measurableSet_singleton w).prod
        ((measurableSet_singleton 1).prod MeasurableSet.univ)),
      Measure.map_apply hobs ((measurableSet_singleton w).prod
        (MeasurableSet.univ.prod MeasurableSet.univ)),
      hpre1 w, hpre2 w, hmuP w true, hmu2 w]
    norm_num
  refine ⟨hprop, ?_⟩
  have hFmeas : AEStronglyMeasurable
      (fun s : Bool × ℝ × ℝ => ((({1} ×ˢ (Set.univ : Set ℝ)).indicator
        (fun _ : ℝ × ℝ => (1 : ℝ)) s.2) * s.2.2 / (1 / 2 : ℝ) -
      ((({0} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ)) s.2) *
        s.2.2 / (1 - 1 / 2 : ℝ)))) (Measure.map (obsDatum obsT obsX obsY0 obsY1)
      (fairCoin.prod fairCoin)) := by
    apply Measurable.aestronglyMeasurable
    have hA1 : Measurable fun s : Bool × ℝ × ℝ =>
        ((({1} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ))) s.2) :=
      (Measurable.indicator measurable_const
        ((measurableSet_singleton (1 : ℝ)).prod MeasurableSet.univ)).comp measurable_snd
    have hA0 : Measurable fun s : Bool × ℝ × ℝ =>
        ((({0} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ))) s.2) :=
      (Measurable.indicator measurable_const
        ((measurableSet_singleton (0 : ℝ)).prod MeasurableSet.univ)).comp measurable_snd
    have hB : Measurable fun s : Bool × ℝ × ℝ => s.2.2 :=
      measurable_snd.comp measurable_snd
    exact ((hA1.mul hB).div_const _).sub ((hA0.mul hB).div_const _)
  have hfun : (fun ω : Bool × Bool => ((({1} ×ˢ (Set.univ : Set ℝ)).indicator
        (fun _ : ℝ × ℝ => (1 : ℝ)) (obsDatum obsT obsX obsY0 obsY1 ω).2) *
        (obsDatum obsT obsX obsY0 obsY1 ω).2.2 / (1 / 2 : ℝ) -
      ((({0} ×ˢ (Set.univ : Set ℝ)).indicator (fun _ : ℝ × ℝ => (1 : ℝ))
        (obsDatum obsT obsX obsY0 obsY1 ω).2) *
        (obsDatum obsT obsX obsY0 obsY1 ω).2.2 / (1 - 1 / 2 : ℝ))))
      = fun ω : Bool × Bool => ((({(true, true)} : Set (Bool × Bool)).indicator
        fun _ => (6 : ℝ)) ω - (({(true, false)} : Set (Bool × Bool)).indicator
        fun _ => (2 : ℝ)) ω) := by
    funext ⟨a, b⟩
    cases a <;> cases b <;>
      simp [hdatum, hXv, hY0v, hY1v, observed, hmemT] <;> norm_num
  have hTT : ({(true, true)} : Set (Bool × Bool)) = {true} ×ˢ ({true} : Set Bool) := by
    ext ⟨a, b⟩
    simp
  have hTF : ({(true, false)} : Set (Bool × Bool)) = {true} ×ˢ ({false} : Set Bool) := by
    ext ⟨a, b⟩
    simp
  have hITT : Integrable (fun ω : Bool × Bool => (({(true, true)} : Set (Bool × Bool)).indicator
      fun _ => (6 : ℝ)) ω) (fairCoin.prod fairCoin) := Integrable.of_finite
  have hITF : Integrable (fun ω : Bool × Bool => (({(true, false)} : Set (Bool × Bool)).indicator
      fun _ => (2 : ℝ)) ω) (fairCoin.prod fairCoin) := Integrable.of_finite
  unfold ipwATE
  simp only [hprop]
  unfold obsLaw
  rw [integral_map hobs.aemeasurable hFmeas, hfun,
    integral_sub hITT hITF,
    integral_indicator_const _ (measurableSet_singleton (true, true)),
    integral_indicator_const _ (measurableSet_singleton (true, false)),
    hTT, hTF]
  unfold Measure.real
  rw [hmuP true true, hmuP true false, smul_eq_mul, smul_eq_mul]
  norm_num

/-- Non-vacuity: treated and control IPW functionals differ for a nontrivial outcome
model. Constant outcomes `0`/`1` under a fair coin give treated value `1`, control `0`. -/
example :
    (∫ ω, (({true} : Set Bool).indicator fun _ => ((1 : ℝ) / (1 / 2 : ℝ))) ω ∂fairCoin) ≠
    (∫ ω, (({true} : Set Bool)ᶜ.indicator fun _ => ((0 : ℝ) / (1 - 1 / 2 : ℝ))) ω ∂fairCoin) := by
  have h1 : (∫ ω, (({true} : Set Bool).indicator fun _ => ((1 : ℝ) / (1 / 2 : ℝ))) ω ∂fairCoin) = 1 := by
    rw [integral_indicator_const _ (measurableSet_singleton true)]
    have hcoin : fairCoin.real {true} = (1/2 : ℝ) := by
      have h : fairCoin {true} = (2 : ENNReal)⁻¹ := by simp [fairCoin]
      unfold Measure.real
      rw [h]
      simp
    rw [hcoin, smul_eq_mul]
    norm_num
  have h0 : (∫ ω, (({true} : Set Bool)ᶜ.indicator fun _ => ((0 : ℝ) / (1 - 1 / 2 : ℝ))) ω ∂fairCoin) = 0 := by
    rw [integral_indicator_const _ (measurableSet_singleton true).compl]
    simp
  rw [h1, h0]
  norm_num

end MathlibExtTest.Probability.Statistics.Identifiability
