/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WaldInequalities
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Shiryaev's theorem: Bayesian optimality of the Shiryaev rule

Let the change point `Γ` have the geometric prior `P(Γ = n) = ρ (1 - ρ)^{n-1}`, `n ≥ 1`, and,
conditional on `Γ`, let the observations be independent, with law `P₀` before `Γ` and law `P₁`
from `Γ` on. `MeasureTheory.shiryaevTime_optimal` states that the Shiryaev rule
`τ_S = inf {n ≥ 1 : pₙ ≥ A}` of `MathlibExt.Probability.Statistics.SequentialAnalysis`, whose
false-alarm probability is `α`, minimises the average detection delay `E[(τ - Γ)⁺]` among all
stopping times `τ` of the observations with false-alarm probability at most `α`
(Veeravalli–Banerjee, Theorem 3.1, crediting Shiryaev 1963 and 1978). The standing assumptions
`P₀ ≠ P₁` and `D(P₁ ‖ P₀) < ∞` of the survey are hypotheses of the statement but are not used by
the proof.

## Proof outline

Write `L = dP₁/dP₀`, `β = 1 - ρ` and `μ = P₀^ℕ`.

* **The criteria under `P₀^ℕ`.** Changing measure on the first `k` observations,
  `PFA(τ) = E_μ[β^τ; τ < ∞]` and `ADD(τ) = ∑_k E_μ[S_k; τ > k]`, where
  `S_k = ∑_{n<k} ρ βⁿ ∏_{n ≤ i < k} L(Xᵢ₊₁)`. With the posterior odds `yₖ = pₖ / (1 - pₖ)`,
  which satisfy `y₀ = 0` and `y_{k+1} = (yₖ + ρ) L(X_{k+1}) / β`, one has `S_k = β^k yₖ`, so
  `λ ADD(τ) + PFA(τ) = E_μ[∑_{k<τ} β^k λ yₖ + β^τ]` is a discounted optimal stopping problem for
  the Markov chain `yₖ`, with running cost `λ y` and stopping cost `1`.
* **Value function.** Backward induction gives a value function `V ≤ 1` of the odds with the
  Bellman equation `V y = min 1 (λ y + β ∫ V ((y + ρ) L / β) dP₀)`. It is monotone and
  `V (t y) ≤ t V y` for `t ≥ 1`, so raising the alarm is optimal exactly on `[B, ∞]`, where `B`
  is the smallest odds with `V B = 1`, and observing is optimal below `B`; above `B` the alarm is
  strictly better, because the running cost `λ y` is strictly increasing.
* **Choice of the cost.** The boundary `B` depends continuously on `λ > 0`, lies between
  `ρ / λ` and `1 / λ`, and so takes the value `A / (1 - A)` for some `λ` by the intermediate value
  theorem; for this `λ` the Shiryaev rule stops exactly when the odds reach or exceed `B`.
* **Verification.** Integrating out the next observation, by induction on `n`, `V 0` is at most
  the expected loss of any stopping time accumulated before `min τ n`, plus `βⁿ`; letting
  `n → ∞` gives `V 0 ≤ λ ADD(τ) + PFA(τ)` with no integrability condition. The Shiryaev rule
  observes only where observing is optimal and stops where `V = 1`, so its loss is `V 0`.
* **Conclusion.** `λ ADD(τ_S) + α ≤ λ ADD(τ) + PFA(τ) ≤ λ ADD(τ) + α`, and `α ≤ 1` cancels.

## References

* V. V. Veeravalli and T. Banerjee, *Quickest change detection*, arXiv:1210.5552v1 (2012),
  §III-A, Theorem 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ### Change of measure for the change-point laws -/

/-- The likelihood ratio `dP₁/dP₀`, read through the reals as in `shiryaevPosterior`. -/
private noncomputable def lrReal (P₀ P₁ : Measure X) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (P₁.rnDeriv P₀ x).toReal

private theorem measurable_lrReal (P₀ P₁ : Measure X) : Measurable (lrReal P₀ P₁) :=
  ENNReal.measurable_ofReal.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal

private theorem withDensity_lrReal (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) : P₀.withDensity (lrReal P₀ P₁) = P₁ := by
  calc P₀.withDensity (lrReal P₀ P₁) = P₀.withDensity (P₁.rnDeriv P₀) := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top P₁ P₀] with x hx
        exact ENNReal.ofReal_toReal hx.ne
    _ = P₁ := Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀

/-- Density of the law of the coordinate `i` under `changePointLaw P₀ P₁ ν`. -/
private noncomputable def cpDens (P₀ P₁ : Measure X) (ν i : ℕ) : X → ℝ≥0∞ :=
  if i + 1 < ν then 1 else lrReal P₀ P₁

private theorem measurable_cpDens (P₀ P₁ : Measure X) (ν i : ℕ) :
    Measurable (cpDens P₀ P₁ ν i) := by
  unfold cpDens
  split_ifs
  · exact measurable_const
  · exact measurable_lrReal P₀ P₁

/-- Change of measure from `P₀^ℕ` to a change-point law on the first `n` observations. -/
private theorem changePointLaw_apply_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (ν n : ℕ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[observationFiltration X n] A) :
    changePointLaw P₀ P₁ ν A = ∫⁻ ω in A, ∏ i ∈ range n, cpDens P₀ P₁ ν i (ω i)
      ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  refine infinitePi_apply_eq_setLIntegral_prod P₀ _ (cpDens P₀ P₁ ν)
    (measurable_cpDens P₀ P₁ ν) (fun i => ?_) n hA
  unfold cpDens
  split_ifs
  · exact withDensity_one.symm
  · exact (withDensity_lrReal P₀ P₁ h₁₀).symm

/-- Before the change, a change-point law is `P₀^ℕ`. -/
private theorem changePointLaw_apply_eq_of_lt (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {ν n : ℕ} (hn : n < ν) {A : Set (ℕ → X)}
    (hA : MeasurableSet[observationFiltration X n] A) :
    changePointLaw P₀ P₁ ν A = Measure.infinitePi (fun _ : ℕ => P₀) A := by
  rw [changePointLaw_apply_eq P₀ P₁ h₁₀ ν n hA, ← setLIntegral_one]
  refine setLIntegral_congr_fun ((observationFiltration X).le n A hA) fun ω _ => ?_
  refine prod_eq_one fun i hi => ?_
  simp [cpDens, show i + 1 < ν by have := mem_range.1 hi; omega]

/-! ### Sums over the geometric prior -/

private theorem tsum_ite_le_eq (g : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' n : ℕ, (if k ≤ n then g n else 0) = ∑' j : ℕ, g (j + k) := by
  rw [← (add_left_injective k).tsum_eq (f := fun n => if k ≤ n then g n else 0)]
  · exact tsum_congr fun j => ite_eq_left (Nat.le_add_left k j)
  · intro n hn
    have hkn : k ≤ n := by
      by_contra h
      exact hn (ite_eq_right h)
    exact ⟨n - k, Nat.sub_add_cancel hkn⟩

private theorem tsum_ite_lt_eq (g : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑' n : ℕ, (if n < k then g n else 0) = ∑ n ∈ range k, g n := by
  rw [tsum_eq_sum (s := range k) fun n hn => ite_eq_right (by simpa using hn)]
  exact sum_congr rfl fun n hn => ite_eq_left (mem_range.1 hn)

/-- The geometric prior puts mass `(1 - ρ)^k` on `{Γ > k}`. -/
private theorem tsum_ite_le_ofReal_geom {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (k : ℕ) :
    ∑' n : ℕ, (if k ≤ n then ENNReal.ofReal (ρ * (1 - ρ) ^ n) else 0) =
      ENNReal.ofReal ((1 - ρ) ^ k) := by
  have h1 : 0 ≤ 1 - ρ := by linarith
  have hρ' : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.2 hρ₀).ne'
  have hterm : ∀ i : ℕ, ENNReal.ofReal (ρ * (1 - ρ) ^ (i + k)) =
      ENNReal.ofReal ((1 - ρ) ^ k) * (ENNReal.ofReal ρ * ENNReal.ofReal (1 - ρ) ^ i) := by
    intro i
    rw [← ENNReal.ofReal_pow h1, ← ENNReal.ofReal_mul hρ₀.le,
      ← ENNReal.ofReal_mul (pow_nonneg h1 _)]
    congr 1
    ring
  rw [tsum_ite_le_eq, tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h1, sub_sub_cancel,
    ENNReal.mul_inv_cancel hρ' ENNReal.ofReal_ne_top, mul_one]

/-! ### The Bayes criteria under `P₀^ℕ` -/

/-- **False-alarm probability under `P₀^ℕ`.** `PFA(τ) = E₀[(1 - ρ)^τ; τ < ∞]`. -/
private theorem falseAlarmProb_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ) :
    falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁ τ = ∑' k : ℕ, ENNReal.ofReal ((1 - ρ) ^ k) *
      Measure.infinitePi (fun _ : ℕ => P₀) {ω | τ ω = k} := by
  set μ := Measure.infinitePi (fun _ : ℕ => P₀)
  have hk : ∀ n : ℕ, changePointLaw P₀ P₁ (n + 1) {ω | τ ω < (n + 1 : ℕ)} =
      ∑' k : ℕ, if k ≤ n then μ {ω | τ ω = k} else 0 := by
    intro n
    have hset : {ω | τ ω < ((n + 1 : ℕ) : WithTop ℕ)} = {ω | τ ω ≤ n} := by
      ext ω
      change (τ ω : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) ↔ (τ ω : ℕ∞) ≤ (n : ℕ∞)
      rw [Nat.cast_add, Nat.cast_one]
      exact ENat.lt_add_one_iff (ENat.natCast_ne_top n)
    rw [hset, changePointLaw_apply_eq_of_lt P₀ P₁ h₁₀ (Nat.lt_add_one n) (by exact hτ n)]
    have hU : {ω | τ ω ≤ n} = ⋃ k ∈ range (n + 1), {ω | τ ω = k} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_range, exists_prop]
      constructor
      · intro h
        induction hτω : τ ω using WithTop.recTopCoe with
        | top => rw [hτω] at h; exact absurd h (by simp)
        | coe m =>
          rw [hτω] at h
          exact ⟨m, by exact_mod_cast Nat.lt_succ_of_le (WithTop.coe_le_coe.1 h), rfl⟩
      · rintro ⟨k, hk, h⟩
        rw [h]
        exact WithTop.coe_le_coe.2 (Nat.le_of_lt_succ hk)
    rw [hU, measure_biUnion_finset]
    · rw [← tsum_ite_lt_eq]
      exact tsum_congr fun k => by simp only [Nat.lt_add_one_iff]; rfl
    · intro i _ j _ hij
      refine Set.disjoint_left.2 fun ω h1 h2 => hij ?_
      have := h1.symm.trans h2
      exact_mod_cast this
    · exact fun k _ => (observationFiltration X).le k _ (hτ.measurableSet_eq k)
  simp_rw [falseAlarmProb, hk, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [tsum_comm]
  refine tsum_congr fun k => ?_
  have hite : ∀ n : ℕ, (if k ≤ n then ENNReal.ofReal (ρ * (1 - ρ) ^ n) * μ {ω | τ ω = k} else 0) =
      (if k ≤ n then ENNReal.ofReal (ρ * (1 - ρ) ^ n) else 0) * μ {ω | τ ω = k} := fun n => by
    split_ifs <;> simp
  rw [tsum_congr hite, ENNReal.tsum_mul_right, tsum_ite_le_ofReal_geom hρ₀ hρ₁]

/-- The posterior mass of a change, unnormalised: `S_k = ∑_{n<k} π_{n+1} ∏_{n ≤ i < k} L(ω i)`. -/
private noncomputable def shirMass (P₀ P₁ : Measure X) (ρ : ℝ) (k : ℕ) (ω : ℕ → X) : ℝ≥0∞ :=
  ∑ n ∈ range k, ENNReal.ofReal (ρ * (1 - ρ) ^ n) * ∏ i ∈ range k, cpDens P₀ P₁ (n + 1) i (ω i)

private theorem enat_lt_sub_iff (t : ℕ∞) (j m : ℕ) :
    (j : ℕ∞) < t - (m : ℕ∞) ↔ ((j + m : ℕ) : ℕ∞) < t := by
  induction t using ENat.recTopCoe with
  | top => simp
  | coe t =>
    rw [← ENat.natCast_sub, Nat.cast_lt, Nat.cast_lt]
    omega

/-- **Average detection delay under `P₀^ℕ`.** `ADD(τ) = ∑_k E₀[S_k; τ > k]`. -/
private theorem averageDetectionDelay_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ) :
    averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁ τ = ∑' k : ℕ, ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω},
      shirMass P₀ P₁ ρ k ω ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  set μ := Measure.infinitePi (fun _ : ℕ => P₀)
  have hS : ∀ k : ℕ, MeasurableSet[observationFiltration X k] {ω | (k : WithTop ℕ) < τ ω} :=
    fun k => hτ.measurableSet_gt k
  have hSm : ∀ k : ℕ, MeasurableSet {ω | (k : WithTop ℕ) < τ ω} := fun k =>
    (observationFiltration X).le k _ (hS k)
  have hn : ∀ n : ℕ, ∫⁻ ω, (((show ℕ∞ from τ ω) - (n + 1 : ℕ) : ℕ∞) : ℝ≥0∞)
      ∂changePointLaw P₀ P₁ (n + 1) = ∑' k : ℕ, if n < k then
        ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω}, ∏ i ∈ range k, cpDens P₀ P₁ (n + 1) i (ω i) ∂μ
        else 0 := by
    intro n
    have hsub : ∀ j : ℕ, {ω | (j : WithTop ℕ) <
        (show WithTop ℕ from ((show ℕ∞ from τ ω) - ((n + 1 : ℕ) : ℕ∞) : ℕ∞))} =
        {ω | ((j + (n + 1) : ℕ) : WithTop ℕ) < τ ω} := fun j =>
      Set.ext fun ω => enat_lt_sub_iff (τ ω) j (n + 1)
    rw [lintegral_enat_eq_tsum
      (T := fun ω => (show WithTop ℕ from ((show ℕ∞ from τ ω) - ((n + 1 : ℕ) : ℕ∞) : ℕ∞))) _
      (fun j => by rw [hsub j]; exact hSm _)]
    simp_rw [hsub]
    rw [← tsum_ite_le_eq (fun k => changePointLaw P₀ P₁ (n + 1) {ω | (k : WithTop ℕ) < τ ω})
      (n + 1)]
    refine tsum_congr fun k => ?_
    by_cases hk : n + 1 ≤ k
    · rw [ite_eq_left hk, ite_eq_left (by omega), changePointLaw_apply_eq P₀ P₁ h₁₀ (n + 1) k
        (hS k)]
    · rw [ite_eq_right hk, ite_eq_right (by omega)]
  simp_rw [averageDetectionDelay, hn, ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [tsum_comm]
  refine tsum_congr fun k => ?_
  rw [tsum_ite_lt_eq]
  unfold shirMass
  have hm : ∀ n : ℕ, Measurable fun ω : ℕ → X => ∏ i ∈ range k, cpDens P₀ P₁ (n + 1) i (ω i) :=
    fun n => Finset.measurable_prod _ fun i _ =>
      (measurable_cpDens P₀ P₁ (n + 1) i).comp (measurable_pi_apply i)
  symm
  rw [lintegral_finsetSum _ (f := fun (n : ℕ) (ω : ℕ → X) => ENNReal.ofReal (ρ * (1 - ρ) ^ n) *
    ∏ i ∈ range k, cpDens P₀ P₁ (n + 1) i (ω i)) fun n _ => measurable_const.mul (hm n)]
  exact sum_congr rfl fun n _ => lintegral_const_mul _ (hm n)

/-! ### The posterior odds -/

/-- One step of the posterior odds `yₙ = pₙ / (1 - pₙ)`:
`y_{n+1} = (yₙ + ρ) L(X_{n+1}) / (1 - ρ)`. -/
private noncomputable def shirStep (P₀ P₁ : Measure X) (ρ : ℝ) (y : ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  (y + ENNReal.ofReal ρ) * lrReal P₀ P₁ x / ENNReal.ofReal (1 - ρ)

/-- The posterior odds `yₙ` of a change, started at `y₀ = 0`. -/
private noncomputable def shirOdds (P₀ P₁ : Measure X) (ρ : ℝ) : ℕ → (ℕ → X) → ℝ≥0∞
  | 0 => fun _ => 0
  | n + 1 => fun ω => shirStep P₀ P₁ ρ (shirOdds P₀ P₁ ρ n ω) (ω n)

private theorem shirStep_mono (P₀ P₁ : Measure X) (ρ : ℝ) {y y' : ℝ≥0∞} (h : y ≤ y') (x : X) :
    shirStep P₀ P₁ ρ y x ≤ shirStep P₀ P₁ ρ y' x := by
  unfold shirStep
  gcongr

private theorem measurable_shirStep (P₀ P₁ : Measure X) (ρ : ℝ) :
    Measurable (Function.uncurry (shirStep P₀ P₁ ρ)) :=
  ((measurable_fst.add measurable_const).mul
    ((measurable_lrReal P₀ P₁).comp measurable_snd)).div_const _

private theorem measurable_shirStep_right (P₀ P₁ : Measure X) (ρ : ℝ) (y : ℝ≥0∞) :
    Measurable (shirStep P₀ P₁ ρ y) :=
  (measurable_const.mul (measurable_lrReal P₀ P₁)).div_const _

private theorem shirStep_mul_le (P₀ P₁ : Measure X) (ρ : ℝ) {t : ℝ≥0∞} (ht : 1 ≤ t)
    (y : ℝ≥0∞) (x : X) : shirStep P₀ P₁ ρ (t * y) x ≤ t * shirStep P₀ P₁ ρ y x := by
  unfold shirStep
  calc (t * y + ENNReal.ofReal ρ) * lrReal P₀ P₁ x / ENNReal.ofReal (1 - ρ)
      ≤ t * (y + ENNReal.ofReal ρ) * lrReal P₀ P₁ x / ENNReal.ofReal (1 - ρ) := by
        gcongr
        rw [mul_add]
        gcongr
        exact le_mul_of_one_le_left' ht
    _ = t * ((y + ENNReal.ofReal ρ) * lrReal P₀ P₁ x / ENNReal.ofReal (1 - ρ)) := by
        rw [mul_assoc, mul_div_assoc, mul_div_assoc]

private theorem measurable_shirOdds (P₀ P₁ : Measure X) (ρ : ℝ) (n : ℕ) :
    Measurable[observationFiltration X n] (shirOdds P₀ P₁ ρ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_shirStep P₀ P₁ ρ).comp
      ((ih.mono ((observationFiltration X).mono (Nat.le_succ n)) le_rfl).prodMk
        (measurable_coord_observationFiltration (Nat.lt_add_one n)))

/-- The unnormalised posterior mass is the discounted posterior odds: `S_k = (1 - ρ)^k y_k`. -/
private theorem shirMass_eq (P₀ P₁ : Measure X) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (k : ℕ)
    (ω : ℕ → X) : shirMass P₀ P₁ ρ k ω = ENNReal.ofReal (1 - ρ) ^ k * shirOdds P₀ P₁ ρ k ω := by
  have h1 : 0 ≤ 1 - ρ := by linarith
  have hβ0 : ENNReal.ofReal (1 - ρ) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hβ : ENNReal.ofReal (1 - ρ) ≠ ∞ := ENNReal.ofReal_ne_top
  induction k with
  | zero => simp [shirMass, shirOdds]
  | succ k ih =>
    have hlast : ∀ n ∈ range (k + 1), ∏ i ∈ range (k + 1), cpDens P₀ P₁ (n + 1) i (ω i) =
        (∏ i ∈ range k, cpDens P₀ P₁ (n + 1) i (ω i)) * lrReal P₀ P₁ (ω k) := by
      intro n hn
      rw [prod_range_succ]
      congr 1
      simp [cpDens, show ¬ k + 1 < n + 1 by have := mem_range.1 hn; omega]
    have hone : ∏ i ∈ range k, cpDens P₀ P₁ (k + 1) i (ω i) = 1 :=
      prod_eq_one fun i hi => by simp [cpDens, show i + 1 < k + 1 by have := mem_range.1 hi; omega]
    calc shirMass P₀ P₁ ρ (k + 1) ω
        = (shirMass P₀ P₁ ρ k ω + ENNReal.ofReal (ρ * (1 - ρ) ^ k)) * lrReal P₀ P₁ (ω k) := by
          simp only [shirMass]
          rw [sum_congr rfl fun n hn => by rw [hlast n hn], sum_range_succ, hone, one_mul, add_mul,
            sum_mul]
          congr 1
          exact sum_congr rfl fun n _ => by rw [mul_assoc]
      _ = ENNReal.ofReal (1 - ρ) ^ (k + 1) * shirOdds P₀ P₁ ρ (k + 1) ω := by
          simp only [shirOdds, shirStep]
          rw [ih, ENNReal.ofReal_mul hρ₀.le, ENNReal.ofReal_pow h1, pow_succ, mul_assoc,
            ENNReal.mul_div_cancel hβ0 hβ]
          ring

/-! ### The value function of the Bayes problem -/

/-- Backward induction for the Bayes problem with horizon `n` in the posterior odds
`y = p / (1 - p)`: raising the alarm costs the posterior probability `1 - p` of a false alarm,
observing once more costs `λ p` of expected delay, and dividing both by `1 - p` gives the costs
`1` and `λ y`; observing discounts the future by `1 - ρ`. -/
private noncomputable def shirIter (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) :
    ℕ → ℝ≥0∞ → ℝ≥0∞
  | 0 => fun _ => 1
  | n + 1 => fun y => min 1 (lam * y + ENNReal.ofReal (1 - ρ) *
      ∫⁻ x, shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ y x) ∂P₀)

private theorem shirIter_le_one (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ) (y : ℝ≥0∞) :
    shirIter P₀ P₁ ρ lam n y ≤ 1 := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_left _ _

private theorem shirIter_mono (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ) :
    Monotone (shirIter P₀ P₁ ρ lam n) := by
  induction n with
  | zero => exact fun _ _ _ => le_rfl
  | succ n ih =>
    intro y y' h
    refine min_le_min_left _ (add_le_add (by gcongr) ?_)
    gcongr with x
    exact ih (shirStep_mono P₀ P₁ ρ h x)

private theorem measurable_shirIter (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ) :
    Measurable (shirIter P₀ P₁ ρ lam n) :=
  (shirIter_mono P₀ P₁ ρ lam n).measurable

private theorem measurable_shirIter_comp (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ)
    (y : ℝ≥0∞) : Measurable fun x => shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ y x) :=
  (measurable_shirIter P₀ P₁ ρ lam n).comp (measurable_shirStep_right P₀ P₁ ρ y)

private theorem shirIter_succ_le (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ)
    (y : ℝ≥0∞) : shirIter P₀ P₁ ρ lam (n + 1) y ≤ shirIter P₀ P₁ ρ lam n y := by
  induction n generalizing y with
  | zero => exact min_le_left _ _
  | succ n ih =>
    refine min_le_min_left _ (add_le_add le_rfl ?_)
    gcongr with x
    exact ih _

private theorem antitone_shirIter (P₀ P₁ : Measure X) (ρ : ℝ) (lam y : ℝ≥0∞) :
    Antitone fun n => shirIter P₀ P₁ ρ lam n y :=
  antitone_nat_of_succ_le fun n => shirIter_succ_le P₀ P₁ ρ lam n y

private theorem shirIter_mul_le (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (y : ℝ≥0∞) :
    shirIter P₀ P₁ ρ lam n (t * y) ≤ t * shirIter P₀ P₁ ρ lam n y := by
  induction n generalizing y with
  | zero => exact le_mul_of_one_le_left' ht
  | succ n ih =>
    simp only [shirIter]
    rw [mul_min, mul_one]
    refine min_le_min ht ?_
    rw [mul_add]
    refine add_le_add (le_of_eq (by ring)) ?_
    calc ENNReal.ofReal (1 - ρ) * ∫⁻ x, shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ (t * y) x) ∂P₀
        ≤ ENNReal.ofReal (1 - ρ) * ∫⁻ x, t * shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ y x) ∂P₀ := by
          gcongr with x
          exact (shirIter_mono P₀ P₁ ρ lam n (shirStep_mul_le P₀ P₁ ρ ht y x)).trans (ih _)
      _ = t * (ENNReal.ofReal (1 - ρ) *
            ∫⁻ x, shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ y x) ∂P₀) := by
          rw [lintegral_const_mul _ (measurable_shirIter_comp P₀ P₁ ρ lam n y)]
          ring

private theorem shirIter_mono_cost (P₀ P₁ : Measure X) (ρ : ℝ) {lam lam' : ℝ≥0∞}
    (h : lam ≤ lam') (n : ℕ) (y : ℝ≥0∞) :
    shirIter P₀ P₁ ρ lam n y ≤ shirIter P₀ P₁ ρ lam' n y := by
  induction n generalizing y with
  | zero => exact le_rfl
  | succ n ih =>
    refine min_le_min_left _ (add_le_add (by gcongr) ?_)
    gcongr with x
    exact ih _

private theorem shirIter_cost_mul_le (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) (n : ℕ)
    {t : ℝ≥0∞} (ht : 1 ≤ t) (y : ℝ≥0∞) :
    shirIter P₀ P₁ ρ (t * lam) n y ≤ t * shirIter P₀ P₁ ρ lam n y := by
  induction n generalizing y with
  | zero => exact le_mul_of_one_le_left' ht
  | succ n ih =>
    simp only [shirIter]
    rw [mul_min, mul_one]
    refine min_le_min ht ?_
    rw [mul_add]
    refine add_le_add (le_of_eq (by ring)) ?_
    calc ENNReal.ofReal (1 - ρ) * ∫⁻ x, shirIter P₀ P₁ ρ (t * lam) n (shirStep P₀ P₁ ρ y x) ∂P₀
        ≤ ENNReal.ofReal (1 - ρ) * ∫⁻ x, t * shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ y x) ∂P₀ := by
          gcongr with x
          exact ih _
      _ = t * (ENNReal.ofReal (1 - ρ) *
            ∫⁻ x, shirIter P₀ P₁ ρ lam n (shirStep P₀ P₁ ρ y x) ∂P₀) := by
          rw [lintegral_const_mul _ (measurable_shirIter_comp P₀ P₁ ρ lam n y)]
          ring

/-- The value function of the Bayes problem with unbounded horizon. -/
private noncomputable def shirValue (P₀ P₁ : Measure X) (ρ : ℝ) (lam y : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ n, shirIter P₀ P₁ ρ lam n y

/-- The expected loss of observing once more and then acting optimally. -/
private noncomputable def shirCont (P₀ P₁ : Measure X) (ρ : ℝ) (lam y : ℝ≥0∞) : ℝ≥0∞ :=
  lam * y + ENNReal.ofReal (1 - ρ) * ∫⁻ x, shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x) ∂P₀

private theorem shirValue_le_one (P₀ P₁ : Measure X) (ρ : ℝ) (lam y : ℝ≥0∞) :
    shirValue P₀ P₁ ρ lam y ≤ 1 :=
  (iInf_le _ 0).trans (shirIter_le_one P₀ P₁ ρ lam 0 y)

private theorem shirValue_mono (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) :
    Monotone (shirValue P₀ P₁ ρ lam) :=
  fun _ _ h => iInf_mono fun n => shirIter_mono P₀ P₁ ρ lam n h

private theorem measurable_shirValue (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) :
    Measurable (shirValue P₀ P₁ ρ lam) :=
  (shirValue_mono P₀ P₁ ρ lam).measurable

private theorem measurable_shirValue_comp (P₀ P₁ : Measure X) (ρ : ℝ) (lam y : ℝ≥0∞) :
    Measurable fun x => shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x) :=
  (measurable_shirValue P₀ P₁ ρ lam).comp (measurable_shirStep_right P₀ P₁ ρ y)

private theorem shirValue_mul_le (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (y : ℝ≥0∞) :
    shirValue P₀ P₁ ρ lam (t * y) ≤ t * shirValue P₀ P₁ ρ lam y := by
  rw [shirValue, shirValue, ENNReal.mul_iInf_of_ne (one_pos.trans_le ht).ne' ht']
  exact iInf_mono fun n => shirIter_mul_le P₀ P₁ ρ lam n ht y

private theorem shirValue_mono_cost (P₀ P₁ : Measure X) (ρ : ℝ) {lam lam' : ℝ≥0∞}
    (h : lam ≤ lam') (y : ℝ≥0∞) : shirValue P₀ P₁ ρ lam y ≤ shirValue P₀ P₁ ρ lam' y :=
  iInf_mono fun n => shirIter_mono_cost P₀ P₁ ρ h n y

private theorem shirValue_cost_mul_le (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) {t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (y : ℝ≥0∞) :
    shirValue P₀ P₁ ρ (t * lam) y ≤ t * shirValue P₀ P₁ ρ lam y := by
  rw [shirValue, shirValue, ENNReal.mul_iInf_of_ne (one_pos.trans_le ht).ne' ht']
  exact iInf_mono fun n => shirIter_cost_mul_le P₀ P₁ ρ lam n ht y

/-- **Bellman equation** for the value function. -/
private theorem shirValue_eq (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {ρ : ℝ} (hρ : ρ < 1)
    (lam y : ℝ≥0∞) : shirValue P₀ P₁ ρ lam y = min 1 (shirCont P₀ P₁ ρ lam y) := by
  have hβ0 : ENNReal.ofReal (1 - ρ) ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hshift : shirValue P₀ P₁ ρ lam y = ⨅ n, shirIter P₀ P₁ ρ lam (n + 1) y :=
    le_antisymm (le_iInf fun n => iInf_le _ (n + 1))
      (iInf_mono fun n => shirIter_succ_le P₀ P₁ ρ lam n y)
  rw [hshift]
  simp only [shirIter, shirCont]
  rw [← inf_iInf, ← ENNReal.add_iInf, ← ENNReal.mul_iInf_of_ne hβ0 ENNReal.ofReal_ne_top]
  congr 3
  simp only [shirValue]
  rw [lintegral_iInf]
  · intro n
    exact measurable_shirIter_comp P₀ P₁ ρ lam n y
  · intro n m hnm x
    exact antitone_shirIter P₀ P₁ ρ lam _ hnm
  · refine ne_top_of_le_ne_top (measure_ne_top P₀ Set.univ) ?_
    rw [← one_mul (P₀ Set.univ), ← lintegral_const]
    exact lintegral_mono fun x => shirIter_le_one P₀ P₁ ρ lam 0 _

private theorem shirValue_le_cont (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {ρ : ℝ}
    (hρ : ρ < 1) (lam y : ℝ≥0∞) : shirValue P₀ P₁ ρ lam y ≤ shirCont P₀ P₁ ρ lam y := by
  rw [shirValue_eq P₀ P₁ hρ]
  exact min_le_right _ _

private theorem lintegral_shirValue_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (ρ : ℝ)
    (lam y : ℝ≥0∞) : ∫⁻ x, shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x) ∂P₀ ≤ 1 := by
  calc ∫⁻ x, shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x) ∂P₀ ≤ ∫⁻ _, 1 ∂P₀ :=
        lintegral_mono fun x => shirValue_le_one P₀ P₁ ρ lam _
    _ = 1 := by simp

private theorem shirCont_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (ρ : ℝ)
    (lam y : ℝ≥0∞) : shirCont P₀ P₁ ρ lam y ≤ lam * y + ENNReal.ofReal (1 - ρ) := by
  unfold shirCont
  gcongr
  calc ENNReal.ofReal (1 - ρ) * ∫⁻ x, shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x) ∂P₀
      ≤ ENNReal.ofReal (1 - ρ) * 1 := by gcongr; exact lintegral_shirValue_le P₀ P₁ ρ lam y
    _ = _ := mul_one _

private theorem integral_term_ne_top (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (ρ : ℝ)
    (lam y : ℝ≥0∞) :
    ENNReal.ofReal (1 - ρ) * ∫⁻ x, shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x) ∂P₀ ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top (lintegral_shirValue_le P₀ P₁ ρ lam y))

/-! ### The alarm boundary -/

/-- The alarm boundary: the smallest posterior odds at which raising the alarm is optimal. -/
private noncomputable def shirBd (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞) : ℝ≥0∞ :=
  sInf {y | shirValue P₀ P₁ ρ lam y = 1}

private theorem shirValue_eq_one_of_lt (P₀ P₁ : Measure X) (ρ : ℝ) {lam y : ℝ≥0∞}
    (hy : shirBd P₀ P₁ ρ lam < y) : shirValue P₀ P₁ ρ lam y = 1 := by
  obtain ⟨y', hy'V, hy'y⟩ := sInf_lt_iff.1 hy
  refine le_antisymm (shirValue_le_one P₀ P₁ ρ lam y) ?_
  calc (1 : ℝ≥0∞) = shirValue P₀ P₁ ρ lam y' := hy'V.symm
    _ ≤ _ := shirValue_mono P₀ P₁ ρ lam hy'y.le

private theorem shirValue_lt_one_of_lt (P₀ P₁ : Measure X) (ρ : ℝ) {lam y : ℝ≥0∞}
    (hy : y < shirBd P₀ P₁ ρ lam) : shirValue P₀ P₁ ρ lam y < 1 :=
  lt_of_le_of_ne (shirValue_le_one P₀ P₁ ρ lam y)
    fun h => (sInf_le (s := {y | shirValue P₀ P₁ ρ lam y = 1}) h).not_gt hy

private theorem shirBd_le_inv (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {ρ : ℝ} (hρ : ρ < 1)
    {lam : ℝ≥0∞} (hlam0 : lam ≠ 0) (hlam : lam ≠ ∞) : shirBd P₀ P₁ ρ lam ≤ lam⁻¹ := by
  refine sInf_le ?_
  change shirValue P₀ P₁ ρ lam lam⁻¹ = 1
  rw [shirValue_eq P₀ P₁ hρ]
  refine min_eq_left ?_
  calc (1 : ℝ≥0∞) = lam * lam⁻¹ := (ENNReal.mul_inv_cancel hlam0 hlam).symm
    _ ≤ _ := le_self_add

private theorem div_le_shirBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ}
    (hρ₁ : ρ < 1) (lam : ℝ≥0∞) : ENNReal.ofReal ρ / lam ≤ shirBd P₀ P₁ ρ lam := by
  refine le_sInf fun y hy => ?_
  change shirValue P₀ P₁ ρ lam y = 1 at hy
  have h1 : (1 : ℝ≥0∞) ≤ lam * y + ENNReal.ofReal (1 - ρ) := by
    rw [← hy, shirValue_eq P₀ P₁ hρ₁]
    exact (min_le_right _ _).trans (shirCont_le P₀ P₁ ρ lam y)
  have h2 : ENNReal.ofReal ρ = 1 - ENNReal.ofReal (1 - ρ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 1 - ρ),
      sub_sub_cancel]
  refine ENNReal.div_le_of_le_mul ?_
  rw [h2, mul_comm]
  exact tsub_le_iff_right.2 h1

private theorem shirBd_pos (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ} (hρ₀ : 0 < ρ)
    (hρ₁ : ρ < 1) {lam : ℝ≥0∞} (hlam : lam ≠ ∞) : 0 < shirBd P₀ P₁ ρ lam :=
  (ENNReal.div_pos (ENNReal.ofReal_pos.2 hρ₀).ne' hlam).trans_le (div_le_shirBd P₀ P₁ hρ₁ lam)

private theorem shirBd_lt_top (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {ρ : ℝ} (hρ : ρ < 1)
    {lam : ℝ≥0∞} (hlam0 : lam ≠ 0) (hlam : lam ≠ ∞) : shirBd P₀ P₁ ρ lam < ∞ :=
  (shirBd_le_inv P₀ P₁ hρ hlam0 hlam).trans_lt (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hlam0))

/-- At the boundary, raising the alarm is optimal. -/
private theorem shirValue_shirBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {lam : ℝ≥0∞} (hlam0 : lam ≠ 0) (hlam : lam ≠ ∞) :
    shirValue P₀ P₁ ρ lam (shirBd P₀ P₁ ρ lam) = 1 := by
  set B := shirBd P₀ P₁ ρ lam
  have hB0 : B ≠ 0 := (shirBd_pos P₀ P₁ hρ₀ hρ₁ hlam).ne'
  have hBtop : B ≠ ∞ := (shirBd_lt_top P₀ P₁ hρ₁ hlam0 hlam).ne
  refine le_antisymm (shirValue_le_one P₀ P₁ ρ lam B)
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
  have hε' : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have ht1 : 1 ≤ 1 + (ε : ℝ≥0∞) := le_self_add
  have httop : 1 + (ε : ℝ≥0∞) ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.coe_ne_top⟩
  have hlt : B < (1 + (ε : ℝ≥0∞)) * B := by
    conv_lhs => rw [← one_mul B]
    exact (ENNReal.mul_lt_mul_iff_left hB0 hBtop).2 (ENNReal.lt_add_right ENNReal.one_ne_top hε')
  calc (1 : ℝ≥0∞) = shirValue P₀ P₁ ρ lam ((1 + (ε : ℝ≥0∞)) * B) :=
        (shirValue_eq_one_of_lt P₀ P₁ ρ hlt).symm
    _ ≤ (1 + (ε : ℝ≥0∞)) * shirValue P₀ P₁ ρ lam B := shirValue_mul_le P₀ P₁ ρ lam ht1 httop B
    _ = shirValue P₀ P₁ ρ lam B + ε * shirValue P₀ P₁ ρ lam B := by ring
    _ ≤ shirValue P₀ P₁ ρ lam B + ε * 1 := by gcongr; exact shirValue_le_one P₀ P₁ ρ lam B
    _ = shirValue P₀ P₁ ρ lam B + ε := by rw [mul_one]

private theorem shirValue_eq_one_of_le (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {lam y : ℝ≥0∞} (hlam0 : lam ≠ 0) (hlam : lam ≠ ∞)
    (hy : shirBd P₀ P₁ ρ lam ≤ y) : shirValue P₀ P₁ ρ lam y = 1 := by
  rcases hy.lt_or_eq with hy | rfl
  · exact shirValue_eq_one_of_lt P₀ P₁ ρ hy
  · exact shirValue_shirBd P₀ P₁ hρ₀ hρ₁ hlam0 hlam

/-- Below the boundary, observing once more is optimal. -/
private theorem shirValue_eq_cont (P₀ P₁ : Measure X) [IsFiniteMeasure P₀] {ρ : ℝ} (hρ : ρ < 1)
    {lam y : ℝ≥0∞} (hy : y < shirBd P₀ P₁ ρ lam) :
    shirValue P₀ P₁ ρ lam y = shirCont P₀ P₁ ρ lam y := by
  have hlt := shirValue_lt_one_of_lt P₀ P₁ ρ hy
  have h := shirValue_eq P₀ P₁ hρ lam y
  rcases le_total 1 (shirCont P₀ P₁ ρ lam y) with hle | hle
  · rw [min_eq_left hle] at h; exact absurd h hlt.ne
  · rwa [min_eq_right hle] at h

/-- Above the boundary, raising the alarm is strictly better than observing. -/
private theorem one_lt_shirCont (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {lam y : ℝ≥0∞} (hlam0 : lam ≠ 0) (hlam : lam ≠ ∞)
    (hy : shirBd P₀ P₁ ρ lam < y) : 1 < shirCont P₀ P₁ ρ lam y := by
  set B := shirBd P₀ P₁ ρ lam
  have hBtop : B ≠ ∞ := (shirBd_lt_top P₀ P₁ hρ₁ hlam0 hlam).ne
  calc (1 : ℝ≥0∞) = shirValue P₀ P₁ ρ lam B := (shirValue_shirBd P₀ P₁ hρ₀ hρ₁ hlam0 hlam).symm
    _ ≤ shirCont P₀ P₁ ρ lam B := shirValue_le_cont P₀ P₁ hρ₁ lam B
    _ < shirCont P₀ P₁ ρ lam y := by
        refine ENNReal.add_lt_add_of_lt_of_le (integral_term_ne_top P₀ P₁ ρ lam B)
          ((ENNReal.mul_lt_mul_iff_right hlam0 hlam).2 hy) ?_
        gcongr with x
        exact shirValue_mono P₀ P₁ ρ lam (shirStep_mono P₀ P₁ ρ hy.le x)

/-! ### Continuity of the boundary in the delay cost -/

private theorem shirValue_le_mul_of_le (P₀ P₁ : Measure X) (ρ : ℝ) {lam lam' t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (h : lam' ≤ t * lam) (y : ℝ≥0∞) :
    shirValue P₀ P₁ ρ lam' y ≤ t * shirValue P₀ P₁ ρ lam y :=
  (shirValue_mono_cost P₀ P₁ ρ h y).trans (shirValue_cost_mul_le P₀ P₁ ρ lam ht ht' y)

private theorem shirCont_le_mul_of_le (P₀ P₁ : Measure X) (ρ : ℝ) {lam lam' t : ℝ≥0∞}
    (ht : 1 ≤ t) (ht' : t ≠ ∞) (h : lam' ≤ t * lam) (y : ℝ≥0∞) :
    shirCont P₀ P₁ ρ lam' y ≤ t * shirCont P₀ P₁ ρ lam y := by
  rw [shirCont, shirCont, mul_add t,
    ← lintegral_const_mul _ (measurable_shirValue_comp P₀ P₁ ρ lam y)]
  refine add_le_add ?_ ?_
  · calc lam' * y ≤ t * lam * y := by gcongr
      _ = t * (lam * y) := mul_assoc _ _ _
  · rw [← lintegral_const_mul _ (measurable_shirValue_comp P₀ P₁ ρ lam' y),
      ← lintegral_const_mul _
        ((measurable_shirValue_comp P₀ P₁ ρ lam y).const_mul (ENNReal.ofReal (1 - ρ)))]
    refine lintegral_mono fun x => ?_
    calc ENNReal.ofReal (1 - ρ) * shirValue P₀ P₁ ρ lam' (shirStep P₀ P₁ ρ y x)
        ≤ ENNReal.ofReal (1 - ρ) * (t * shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x)) := by
          gcongr; exact shirValue_le_mul_of_le P₀ P₁ ρ ht ht' h _
      _ = t * (ENNReal.ofReal (1 - ρ) * shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x)) := by ring

private theorem ofReal_le_ofReal_max_mul {c₀ : ℝ} (hc₀ : 0 < c₀) (c : ℝ) :
    ENNReal.ofReal c ≤ ENNReal.ofReal (max 1 (c / c₀)) * ENNReal.ofReal c₀ := by
  rw [← ENNReal.ofReal_mul (le_max_of_le_left zero_le_one)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc c = c / c₀ * c₀ := (div_mul_cancel₀ c hc₀.ne').symm
    _ ≤ max 1 (c / c₀) * c₀ := mul_le_mul_of_nonneg_right (le_max_right _ _) hc₀.le

private theorem tendsto_ofReal_max_mul {c₀ : ℝ} {z : ℝ≥0∞} (hz : z ≠ ∞)
    {f : ℝ → ℝ} (hf : ContinuousAt f c₀) (hf₀ : f c₀ = 1) :
    Tendsto (fun c : ℝ => ENNReal.ofReal (max 1 (f c)) * z) (𝓝 c₀) (𝓝 z) := by
  have h1 : ContinuousAt (fun c : ℝ => max 1 (f c)) c₀ := continuousAt_const.max hf
  have := ENNReal.Tendsto.mul_const (b := z)
    (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto (Or.inr hz)
  simpa [hf₀] using this

private theorem eventually_shirValue_lt (P₀ P₁ : Measure X) (ρ : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {y z : ℝ≥0∞} (h : shirValue P₀ P₁ ρ (ENNReal.ofReal c₀) y < z) :
    ∀ᶠ c in 𝓝 c₀, shirValue P₀ P₁ ρ (ENNReal.ofReal c) y < z := by
  have hv : shirValue P₀ P₁ ρ (ENNReal.ofReal c₀) y ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (shirValue_le_one P₀ P₁ ρ _ y)
  have hT := tendsto_ofReal_max_mul hv (f := fun c => c / c₀)
    (continuousAt_id.div_const c₀) (div_self hc₀.ne')
  filter_upwards [hT.eventually_lt_const h] with c hc
  exact (shirValue_le_mul_of_le P₀ P₁ ρ (ENNReal.one_le_ofReal.2 (le_max_left _ _))
    ENNReal.ofReal_ne_top (ofReal_le_ofReal_max_mul hc₀ c) y).trans_lt hc

private theorem eventually_lt_shirCont (P₀ P₁ : Measure X) (ρ : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {y z : ℝ≥0∞} (hz : z ≠ ∞) (h : z < shirCont P₀ P₁ ρ (ENNReal.ofReal c₀) y) :
    ∀ᶠ c in 𝓝 c₀, z < shirCont P₀ P₁ ρ (ENNReal.ofReal c) y := by
  have hT := tendsto_ofReal_max_mul hz (f := fun c => c₀ / c)
    (continuousAt_const.div continuousAt_id hc₀.ne') (div_self hc₀.ne')
  filter_upwards [hT.eventually_lt_const h, eventually_gt_nhds hc₀] with c hc hcpos
  have ht1 : 1 ≤ ENNReal.ofReal (max 1 (c₀ / c)) := ENNReal.one_le_ofReal.2 (le_max_left _ _)
  have hle := shirCont_le_mul_of_le P₀ P₁ ρ ht1 ENNReal.ofReal_ne_top
    (ofReal_le_ofReal_max_mul hcpos c₀) y
  exact (ENNReal.mul_lt_mul_iff_right (zero_lt_one.trans_le ht1).ne' ENNReal.ofReal_ne_top).1
    (hc.trans_le hle)

private theorem continuousAt_shirBd (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ContinuousAt (fun c : ℝ => (shirBd P₀ P₁ ρ (ENNReal.ofReal c)).toReal) c₀ := by
  have hfin : ∀ᶠ c in 𝓝 c₀, shirBd P₀ P₁ ρ (ENNReal.ofReal c) ≠ ∞ := by
    filter_upwards [eventually_gt_nhds hc₀] with c hc
    exact (shirBd_lt_top P₀ P₁ hρ₁ (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top).ne
  have hB₀ : shirBd P₀ P₁ ρ (ENNReal.ofReal c₀) ≠ ∞ :=
    (shirBd_lt_top P₀ P₁ hρ₁ (ENNReal.ofReal_pos.2 hc₀).ne' ENNReal.ofReal_ne_top).ne
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · rcases lt_or_ge a' 0 with ha0 | ha0
    · exact Eventually.of_forall fun c => ha0.trans_le ENNReal.toReal_nonneg
    obtain ⟨a'', ha'a'', ha''⟩ := exists_between ha'
    have ha0' : 0 ≤ a'' := ha0.trans ha'a''.le
    have hy : ENNReal.ofReal a'' < shirBd P₀ P₁ ρ (ENNReal.ofReal c₀) :=
      (ENNReal.ofReal_lt_iff_lt_toReal ha0' hB₀).2 ha''
    have hV := shirValue_lt_one_of_lt P₀ P₁ ρ hy
    filter_upwards [eventually_shirValue_lt P₀ P₁ ρ hc₀ hV, hfin] with c hc hcfin
    have hle : ENNReal.ofReal a'' ≤ shirBd P₀ P₁ ρ (ENNReal.ofReal c) :=
      not_lt.1 fun h => hc.ne (shirValue_eq_one_of_lt P₀ P₁ ρ h)
    calc a' < a'' := ha'a''
      _ = (ENNReal.ofReal a'').toReal := (ENNReal.toReal_ofReal ha0').symm
      _ ≤ _ := ENNReal.toReal_mono hcfin hle
  · obtain ⟨a'', ha'a'', ha''⟩ := exists_between ha'
    have hy : shirBd P₀ P₁ ρ (ENNReal.ofReal c₀) < ENNReal.ofReal a'' :=
      (ENNReal.lt_ofReal_iff_toReal_lt hB₀).2 ha'a''
    have hcont := one_lt_shirCont P₀ P₁ hρ₀ hρ₁ (ENNReal.ofReal_pos.2 hc₀).ne'
      ENNReal.ofReal_ne_top hy
    filter_upwards [eventually_lt_shirCont P₀ P₁ ρ hc₀ ENNReal.one_ne_top hcont] with c hc
    have hV : shirValue P₀ P₁ ρ (ENNReal.ofReal c) (ENNReal.ofReal a'') = 1 := by
      rw [shirValue_eq P₀ P₁ hρ₁, min_eq_left hc.le]
    have hle : shirBd P₀ P₁ ρ (ENNReal.ofReal c) ≤ ENNReal.ofReal a'' := sInf_le hV
    calc (shirBd P₀ P₁ ρ (ENNReal.ofReal c)).toReal ≤ (ENNReal.ofReal a'').toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = a'' := ENNReal.toReal_ofReal (ENNReal.toReal_nonneg.trans ha'a''.le)
      _ < a' := ha''

/-- **Choice of the delay cost.** Every positive threshold of the posterior odds is the alarm
boundary of the Bayes problem for some delay cost. -/
private theorem exists_shirBd_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {b : ℝ} (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ (shirBd P₀ P₁ ρ (ENNReal.ofReal c)).toReal = b := by
  set c₁ := ρ / b
  set c₂ := 1 / b
  have hc₁ : 0 < c₁ := div_pos hρ₀ hb
  have hc₂ : 0 < c₂ := div_pos one_pos hb
  have hc₁₂ : c₁ ≤ c₂ := div_le_div_of_nonneg_right hρ₁.le hb.le
  set F : ℝ → ℝ := fun c => (shirBd P₀ P₁ ρ (ENNReal.ofReal c)).toReal
  have hF₁ : b ≤ F c₁ := by
    have h := div_le_shirBd P₀ P₁ (ρ := ρ) hρ₁ (ENNReal.ofReal c₁)
    rw [← ENNReal.ofReal_div_of_pos hc₁, div_div_cancel₀ hρ₀.ne'] at h
    have hfin := (shirBd_lt_top P₀ P₁ hρ₁ (ENNReal.ofReal_pos.2 hc₁).ne'
      ENNReal.ofReal_ne_top).ne
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h
  have hF₂ : F c₂ ≤ b := by
    have h := shirBd_le_inv P₀ P₁ (ρ := ρ) hρ₁ (ENNReal.ofReal_pos.2 hc₂).ne'
      ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_inv_of_pos hc₂, show c₂⁻¹ = b by simp [c₂]] at h
    exact ENNReal.toReal_le_of_le_ofReal hb.le h
  have hcont : ContinuousOn F (Set.Icc c₁ c₂) := fun c hc =>
    (continuousAt_shirBd P₀ P₁ hρ₀ hρ₁ (hc₁.trans_le hc.1)).continuousWithinAt
  obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc' hc₁₂ hcont ⟨hF₂, hF₁⟩
  exact ⟨c, hc₁.trans_le hc.1, hFc⟩

/-! ### The potential argument -/

/-- Expected delay cost at step `k` of a stopping time `τ`. -/
private noncomputable def shirStepCost (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞)
    (τ : (ℕ → X) → WithTop ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (k : WithTop ℕ) < τ ω},
    lam * (ENNReal.ofReal (1 - ρ) ^ k * shirOdds P₀ P₁ ρ k ω) ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Discounted value of the state at which `τ` stops, on the event `{τ = k}`. -/
private noncomputable def shirStopValue (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞)
    (τ : (ℕ → X) → WithTop ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | τ ω = k}, ENNReal.ofReal (1 - ρ) ^ k * shirValue P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ k ω)
    ∂Measure.infinitePi (fun _ : ℕ => P₀)

/-- Discounted value of the state at time `n` on the event that `τ` has not stopped before `n`. -/
private noncomputable def shirRemValue (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞)
    (τ : (ℕ → X) → WithTop ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (n : WithTop ℕ) ≤ τ ω},
    ENNReal.ofReal (1 - ρ) ^ n * shirValue P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ n ω)
      ∂Measure.infinitePi (fun _ : ℕ => P₀)

private theorem shirRemValue_eq (P₀ P₁ : Measure X) (ρ : ℝ) (lam : ℝ≥0∞)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ) (n : ℕ) :
    shirRemValue P₀ P₁ ρ lam τ n = shirStopValue P₀ P₁ ρ lam τ n +
      ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω},
        ENNReal.ofReal (1 - ρ) ^ n * shirValue P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ n ω)
          ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  have hset : {ω | (n : WithTop ℕ) ≤ τ ω} = {ω | τ ω = n} ∪ {ω | (n : WithTop ℕ) < τ ω} := by
    ext ω; simp only [Set.mem_union, Set.mem_ofPred_eq, le_iff_eq_or_lt, eq_comm]
  have hS : MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < τ ω} :=
    hτ.measurableSet_gt n
  rw [shirRemValue, shirStopValue, hset, lintegral_union ((observationFiltration X).le n _ hS)]
  refine Set.disjoint_left.2 fun ω h1 h2 => ?_
  simp only [Set.mem_ofPred_eq] at h1 h2
  rw [h1] at h2
  exact lt_irrefl _ h2

private theorem setLIntegral_shirCont_eq (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (ρ : ℝ)
    (lam : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ)
    (n : ℕ) :
    ∫⁻ ω in {ω | (n : WithTop ℕ) < τ ω},
        ENNReal.ofReal (1 - ρ) ^ n * shirCont P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ n ω)
          ∂Measure.infinitePi (fun _ : ℕ => P₀) =
      shirStepCost P₀ P₁ ρ lam τ n + shirRemValue P₀ P₁ ρ lam τ (n + 1) := by
  have hY := measurable_shirOdds P₀ P₁ ρ n
  have hYm : Measurable (shirOdds P₀ P₁ ρ n) := hY.mono ((observationFiltration X).le n) le_rfl
  have hh : Measurable (Function.uncurry fun y x =>
      ENNReal.ofReal (1 - ρ) ^ (n + 1) * shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ y x)) :=
    measurable_const.mul ((measurable_shirValue P₀ P₁ ρ lam).comp (measurable_shirStep P₀ P₁ ρ))
  have hpt : ∀ ω, ENNReal.ofReal (1 - ρ) ^ n * shirCont P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ n ω) =
      lam * (ENNReal.ofReal (1 - ρ) ^ n * shirOdds P₀ P₁ ρ n ω) + ∫⁻ x,
        ENNReal.ofReal (1 - ρ) ^ (n + 1) *
          shirValue P₀ P₁ ρ lam (shirStep P₀ P₁ ρ (shirOdds P₀ P₁ ρ n ω) x) ∂P₀ := by
    intro ω
    rw [shirCont, lintegral_const_mul _ (measurable_shirValue_comp P₀ P₁ ρ lam _)]
    ring
  have hS : MeasurableSet[observationFiltration X n] {ω | (n : WithTop ℕ) < τ ω} :=
    hτ.measurableSet_gt n
  simp only [hpt]
  rw [lintegral_add_left (f := fun ω => lam * (ENNReal.ofReal (1 - ρ) ^ n * shirOdds P₀ P₁ ρ n ω))
    (measurable_const.mul (measurable_const.mul hYm)), shirStepCost,
    shirRemValue, setOfPred_natCast_add_one_le_eq,
    ← setLIntegral_infinitePi_coord P₀ n hS hY hh]
  rfl

private theorem shirRemValue_zero (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] (ρ : ℝ)
    (lam : ℝ≥0∞) (τ : (ℕ → X) → WithTop ℕ) :
    shirRemValue P₀ P₁ ρ lam τ 0 = shirValue P₀ P₁ ρ lam 0 := by
  simp [shirRemValue, shirOdds]

/-- For any stopping time `τ` and horizon `n`, the value at the initial odds `0` is at most the
expected delay cost of `τ` before `min τ n`, plus the discounted value at the odds where `τ` stops
before `n`, plus the discounted value at time `n` on `{n ≤ τ}`. -/
private theorem shirValue_le_sum_add_remValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    {ρ : ℝ} (hρ : ρ < 1) (lam : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (observationFiltration X) τ) (n : ℕ) :
    shirValue P₀ P₁ ρ lam 0 ≤ ∑ k ∈ range n,
      (shirStepCost P₀ P₁ ρ lam τ k + shirStopValue P₀ P₁ ρ lam τ k) +
        shirRemValue P₀ P₁ ρ lam τ n := by
  induction n with
  | zero => simp [shirRemValue_zero]
  | succ n ih =>
    refine ih.trans ?_
    rw [sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    rw [shirRemValue_eq P₀ P₁ ρ lam hτ, add_comm (shirStepCost _ _ _ _ _ _), add_assoc,
      ← setLIntegral_shirCont_eq P₀ P₁ ρ lam hτ]
    refine add_le_add le_rfl (lintegral_mono fun ω => ?_)
    gcongr
    exact shirValue_le_cont P₀ P₁ hρ lam _

/-- If observing is optimal at the odds of every time at which `τ` continues, the bound of
`shirValue_le_sum_add_remValue` is reversed: the expected delay cost of `τ` before `min τ n`,
plus the discounted value at the odds where `τ` stops before `n`, plus the discounted value at
time `n` on `{n ≤ τ}`, is at most the value at the initial odds `0`. This is the expected loss of
`τ` only if, moreover, raising the alarm is optimal where `τ` stops (`risk_le_shirValue`). -/
private theorem sum_add_remValue_le_shirValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    (ρ : ℝ) (lam : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (observationFiltration X) τ)
    (hcont : ∀ n : ℕ, ∀ ω, (n : WithTop ℕ) < τ ω →
      shirCont P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ n ω) ≤ shirValue P₀ P₁ ρ lam (shirOdds P₀ P₁ ρ n ω))
    (n : ℕ) :
    ∑ k ∈ range n, (shirStepCost P₀ P₁ ρ lam τ k + shirStopValue P₀ P₁ ρ lam τ k) +
      shirRemValue P₀ P₁ ρ lam τ n ≤ shirValue P₀ P₁ ρ lam 0 := by
  induction n with
  | zero => simp [shirRemValue_zero]
  | succ n ih =>
    refine le_trans ?_ ih
    rw [sum_range_succ, add_assoc]
    refine add_le_add le_rfl ?_
    rw [shirRemValue_eq P₀ P₁ ρ lam hτ n, add_comm (shirStepCost _ _ _ _ _ _), add_assoc,
      ← setLIntegral_shirCont_eq P₀ P₁ ρ lam hτ]
    refine add_le_add le_rfl (setLIntegral_mono' ((observationFiltration X).le n _
      (hτ.measurableSet_gt n)) fun ω hω => ?_)
    gcongr
    exact hcont n ω hω

private theorem tsum_shirStepCost (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (lam : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ) :
    ∑' k, shirStepCost P₀ P₁ ρ lam τ k =
      lam * averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τ := by
  rw [averageDetectionDelay_eq P₀ P₁ h₁₀ hρ₀ hρ₁.le hτ, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hm : Measurable fun ω => ENNReal.ofReal (1 - ρ) ^ k * shirOdds P₀ P₁ ρ k ω :=
    measurable_const.mul ((measurable_shirOdds P₀ P₁ ρ k).mono ((observationFiltration X).le k)
      le_rfl)
  rw [shirStepCost, lintegral_const_mul _ hm]
  congr 1
  refine setLIntegral_congr_fun ((observationFiltration X).le k _
    (hτ.measurableSet_gt k)) fun ω _ => (shirMass_eq P₀ P₁ hρ₀ hρ₁ k ω).symm

/-- **Lower bound for the Bayes risk of any stopping time.** -/
private theorem shirValue_le_risk (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    (lam : ℝ≥0∞) {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ) :
    shirValue P₀ P₁ ρ lam 0 ≤ lam * averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τ +
      falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁.le τ := by
  set β := ENNReal.ofReal (1 - ρ) with hβ
  have hβ1 : β < 1 := by
    rw [hβ, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  set S := ∑' k, (shirStepCost P₀ P₁ ρ lam τ k + shirStopValue P₀ P₁ ρ lam τ k) with hS
  have hbound : ∀ n : ℕ, shirValue P₀ P₁ ρ lam 0 ≤ S + β ^ n := by
    intro n
    refine (shirValue_le_sum_add_remValue P₀ P₁ hρ₁ lam hτ n).trans
      (add_le_add (sum_le_tsum _) ?_)
    calc shirRemValue P₀ P₁ ρ lam τ n ≤ ∫⁻ _ in {ω | (n : WithTop ℕ) ≤ τ ω}, β ^ n
          ∂Measure.infinitePi (fun _ : ℕ => P₀) :=
          lintegral_mono fun ω => mul_le_of_le_one_right' (shirValue_le_one P₀ P₁ ρ lam _)
      _ = β ^ n * Measure.infinitePi (fun _ : ℕ => P₀) {ω | (n : WithTop ℕ) ≤ τ ω} :=
          setLIntegral_const _ _
      _ ≤ β ^ n * 1 := by gcongr; exact prob_le_one
      _ = β ^ n := mul_one _
  have htend : Tendsto (fun n : ℕ => S + β ^ n) atTop (𝓝 S) := by
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hβ1)
  refine (ge_of_tendsto' htend hbound).trans ?_
  rw [hS, tsum_add, tsum_shirStepCost P₀ P₁ h₁₀ hρ₀ hρ₁ lam hτ,
    falseAlarmProb_eq P₀ P₁ h₁₀ hρ₀ hρ₁.le hτ]
  refine add_le_add le_rfl (tsum_le_tsum fun k => ?_)
  rw [shirStopValue, ENNReal.ofReal_pow (by linarith), ← setLIntegral_const]
  exact lintegral_mono fun ω => mul_le_of_le_one_right' (shirValue_le_one P₀ P₁ ρ lam _)

/-- **A threshold rule at the alarm boundary attains the Bayes value.** -/
private theorem risk_le_shirValue (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1)
    {lam : ℝ≥0∞} (hlam0 : lam ≠ 0) (hlam : lam ≠ ∞) {τ : (ℕ → X) → WithTop ℕ}
    (hτ : IsStoppingTime (observationFiltration X) τ)
    (hcont : ∀ (n : ℕ) ω, (n : WithTop ℕ) < τ ω → shirOdds P₀ P₁ ρ n ω < shirBd P₀ P₁ ρ lam)
    (hstop : ∀ (n : ℕ) ω, τ ω = n → shirBd P₀ P₁ ρ lam ≤ shirOdds P₀ P₁ ρ n ω) :
    lam * averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τ + falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁.le τ ≤
      shirValue P₀ P₁ ρ lam 0 := by
  have hsum : ∑' k, (shirStepCost P₀ P₁ ρ lam τ k + shirStopValue P₀ P₁ ρ lam τ k) ≤
      shirValue P₀ P₁ ρ lam 0 :=
    ENNReal.tsum_le_of_sum_range_le fun n => le_self_add.trans
      (sum_add_remValue_le_shirValue P₀ P₁ ρ lam hτ
        (fun n ω h => (shirValue_eq_cont P₀ P₁ hρ₁ (hcont n ω h)).ge) n)
  rw [tsum_add, tsum_shirStepCost P₀ P₁ h₁₀ hρ₀ hρ₁ lam hτ] at hsum
  refine le_trans (le_of_eq ?_) hsum
  rw [falseAlarmProb_eq P₀ P₁ h₁₀ hρ₀ hρ₁.le hτ]
  congr 1
  refine tsum_congr fun k => ?_
  rw [shirStopValue, ENNReal.ofReal_pow (by linarith), ← setLIntegral_const]
  refine (setLIntegral_congr_fun ((observationFiltration X).le k _ (hτ.measurableSet_eq k))
    fun ω hω => ?_).symm
  rw [shirValue_eq_one_of_le P₀ P₁ hρ₀ hρ₁ hlam0 hlam (hstop k ω hω), mul_one]

/-! ### Shiryaev's statistic -/

private theorem shiryaevPosterior_succ (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (ρ : ℝ) (hρ₀ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (k : ℕ) (ω : ℕ → X) :
    shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ (k + 1) ω =
      (shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ k ω +
          (1 - shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ k ω) * ρ) *
        (P₁.rnDeriv P₀ (ω k)).toReal /
      ((shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ k ω +
          (1 - shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ k ω) * ρ) *
        (P₁.rnDeriv P₀ (ω k)).toReal +
        (1 - (shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ k ω +
          (1 - shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ k ω) * ρ))) :=
  rfl

/-- The posterior probability lies in `[0, 1)` and the posterior odds are `pₙ / (1 - pₙ)`. -/
private theorem shiryaevPosterior_spec (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) {ρ : ℝ} (hρ₀ : 0 < ρ)
    (hρ₁ : ρ < 1) (k : ℕ) (ω : ℕ → X) :
    0 ≤ shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le k ω ∧
      shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le k ω < 1 ∧
      shirOdds P₀ P₁ ρ k ω = ENNReal.ofReal (shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le k ω /
        (1 - shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le k ω)) := by
  induction k with
  | zero => simp [shiryaevPosterior, shirOdds]
  | succ k ih =>
    obtain ⟨hp0, hp1, hy⟩ := ih
    rw [shiryaevPosterior_succ]
    set p := shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le k ω with hp
    set L := (P₁.rnDeriv P₀ (ω k)).toReal with hL
    have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
    set q := p + (1 - p) * ρ with hq
    have hq0 : 0 ≤ q := add_nonneg hp0 (mul_nonneg (by linarith) hρ₀.le)
    have hq1' : 1 - q = (1 - p) * (1 - ρ) := by rw [hq]; ring
    have hq1 : 0 < 1 - q := by rw [hq1']; exact mul_pos (by linarith) (by linarith)
    have hD : 0 < q * L + (1 - q) := by nlinarith [mul_nonneg hq0 hL0]
    refine ⟨div_nonneg (mul_nonneg hq0 hL0) hD.le, (div_lt_one hD).2 (by linarith), ?_⟩
    simp only [shirOdds, shirStep, lrReal]
    rw [hy, ← ENNReal.ofReal_add (div_nonneg hp0 (by linarith)) hρ₀.le,
      ← ENNReal.ofReal_mul (add_nonneg (div_nonneg hp0 (by linarith)) hρ₀.le),
      ← ENNReal.ofReal_div_of_pos (by linarith)]
    congr 1
    have h1p : 1 - p ≠ 0 := by linarith
    have h1ρ : 1 - ρ ≠ 0 := by linarith
    have hsub : 1 - q * L / (q * L + (1 - q)) = (1 - q) / (q * L + (1 - q)) := by
      field_simp
      ring
    rw [hsub, div_div_div_cancel_right₀ hD.ne', hq1']
    rw [hq]
    field_simp
    ring

private theorem adapted_shiryaevPosterior (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (ρ : ℝ) (hρ₀ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) :
    Adapted (observationFiltration X) (shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁) := by
  intro n
  change Measurable[observationFiltration X n] (shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ n)
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hp : Measurable[observationFiltration X (n + 1)]
        (shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ n) :=
      ih.mono ((observationFiltration X).mono (Nat.le_succ n)) le_rfl
    have hL : Measurable[observationFiltration X (n + 1)]
        fun ω : ℕ → X => (P₁.rnDeriv P₀ (ω n)).toReal :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal.comp
        (measurable_coord_observationFiltration (Nat.lt_add_one n))
    have hq : Measurable[observationFiltration X (n + 1)] fun ω =>
        shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ n ω +
          (1 - shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁ n ω) * ρ :=
      hp.add ((measurable_const.sub hp).mul measurable_const)
    exact (hq.mul hL).div ((hq.mul hL).add (measurable_const.sub hq))

/-! ### Shiryaev's theorem -/

-- The statement keeps the standing assumptions `P₀ ≠ P₁` and `D(P₁ ‖ P₀) < ∞` of the source;
-- the proof does not use them.
set_option linter.unusedVariables false in
/-- **Shiryaev's theorem: Bayesian optimality of the Shiryaev rule.** Let `P₀ ≠ P₁` be mutually
absolutely continuous with `D(P₁ ‖ P₀) < ∞`, let the change point have the geometric prior
`ρ (1 - ρ)^{n-1}` with `0 < ρ < 1`, and let `0 < A < 1` be a threshold whose Shiryaev rule
`τ_S = inf {n ≥ 1 : pₙ ≥ A}` has false-alarm probability exactly `α`. Then `τ_S` minimises the
average detection delay `E[(τ - Γ)⁺]` among all stopping times `τ` with false-alarm probability
`P(τ < Γ) ≤ α` (Veeravalli–Banerjee, Theorem 3.1, crediting Shiryaev 1963 and 1978; the
hypotheses `P₀ ≠ P₁` and `D(P₁ ‖ P₀) < ∞` are that survey's standing assumption
`0 < D(f₁ ‖ f₀) < ∞`). -/
theorem shiryaevTime_optimal {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (hne : P₀ ≠ P₁)
    (hkl : InformationTheory.klDiv P₁ P₀ ≠ ∞) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) {A : ℝ}
    (hA₀ : 0 < A) (hA₁ : A < 1) {α : ℝ≥0∞}
    (hα : falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁.le (shiryaevTime P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le A) = α)
    {τ : (ℕ → X) → WithTop ℕ} (hτ : IsStoppingTime (observationFiltration X) τ)
    (hτα : falseAlarmProb P₀ P₁ ρ hρ₀ hρ₁.le τ ≤ α) :
    averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le (shiryaevTime P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le A) ≤
      averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τ := by
  set u := shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le with hu
  set τS := shiryaevTime P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le A with hτSdef
  have hτS : IsStoppingTime (observationFiltration X) τS :=
    (adapted_shiryaevPosterior P₀ P₁ h₁₀ h₀₁ ρ hρ₀ hρ₁.le).isStoppingTime_hittingAfter
      measurableSet_Ici
  have hb : 0 < A / (1 - A) := div_pos hA₀ (by linarith)
  obtain ⟨c, hc, hB⟩ := exists_shirBd_eq P₀ P₁ hρ₀ hρ₁ hb
  set lam := ENNReal.ofReal c
  have hlam0 : lam ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hlam : lam ≠ ∞ := ENNReal.ofReal_ne_top
  have hBeq : shirBd P₀ P₁ ρ lam = ENNReal.ofReal (A / (1 - A)) := by
    rw [← hB, ENNReal.ofReal_toReal (shirBd_lt_top P₀ P₁ hρ₁ hlam0 hlam).ne]
  have hodds : ∀ (k : ℕ) ω, A ≤ u k ω ↔ ENNReal.ofReal (A / (1 - A)) ≤ shirOdds P₀ P₁ ρ k ω := by
    intro k ω
    obtain ⟨hp0, hp1, hy⟩ := shiryaevPosterior_spec P₀ P₁ h₁₀ h₀₁ hρ₀ hρ₁ k ω
    rw [hy, ENNReal.ofReal_le_ofReal_iff (div_nonneg hp0 (by linarith)),
      div_le_div_iff₀ (by linarith) (by linarith)]
    constructor <;> intro h <;> nlinarith
  have hcont : ∀ (n : ℕ) ω, (n : WithTop ℕ) < τS ω →
      shirOdds P₀ P₁ ρ n ω < shirBd P₀ P₁ ρ lam := by
    intro n ω h
    rw [hBeq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [shirOdds] using hb
    · have hnot := notMem_of_lt_hittingAfter (u := u) (s := Set.Ici A) (n := 1) h hn
      rw [Set.mem_Ici, hodds] at hnot
      exact not_le.1 hnot
  have hstop : ∀ (n : ℕ) ω, τS ω = n → shirBd P₀ P₁ ρ lam ≤ shirOdds P₀ P₁ ρ n ω := by
    intro n ω h
    rw [hBeq, ← hodds]
    have h' : hittingAfter u (Set.Ici A) 1 ω = n := h
    have hne' : hittingAfter u (Set.Ici A) 1 ω ≠ ⊤ := by rw [h']; exact WithTop.coe_ne_top
    have hmem := hittingAfter_mem_set_of_ne_top hne'
    rw [h'] at hmem
    exact hmem
  have h1 := risk_le_shirValue P₀ P₁ h₁₀ hρ₀ hρ₁ hlam0 hlam hτS hcont hstop
  have h2 := shirValue_le_risk P₀ P₁ h₁₀ hρ₀ hρ₁ lam hτ
  have hαtop : α ≠ ∞ := by
    rw [← hα]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_add_self.trans (h1.trans (shirValue_le_one P₀ P₁ ρ lam 0)))
  have h3 : lam * averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τS + α ≤
      lam * averageDetectionDelay P₀ P₁ ρ hρ₀ hρ₁.le τ + α := by
    rw [← hα] at hτα ⊢
    exact h1.trans (h2.trans (add_le_add le_rfl hτα))
  exact (ENNReal.mul_le_mul_iff_right hlam0 hlam).1 (ENNReal.le_of_add_le_add_right hαtop h3)

end MeasureTheory
