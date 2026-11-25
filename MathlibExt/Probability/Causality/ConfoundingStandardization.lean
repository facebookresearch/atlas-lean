/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.ConfoundingBounds
public import MathlibExt.Probability.Causality.Standardization

/-!
# Probability and causal interpretations of finite confounding bounds

The observed joint law determines the conditional risks on positive exposure
cells. The whole-population standardization uses the supplied version on
null cells. Consistency, joint conditional exchangeability and strict overlap
give a causal interpretation through the finite g-formula.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A binary variable represented by its event for the value `true`. -/
def binaryEvent {Ω : Type*} (T : Set Ω) (e : Bool) : Set Ω :=
  if e then T else Tᶜ

namespace FiniteRiskModel

/-- The measurable observation agrees with the kernel model on every atom of
the joint law of exposure, confounder and outcome. -/
def HasJointLaw {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (m : FiniteRiskModel n)
    (μ : Measure Ω) (T D : Set Ω) (U : Ω → Fin (n + 1)) : Prop :=
  ∀ e u d, μ.real (binaryEvent T e ∩ U ⁻¹' {u} ∩ binaryEvent D d) = m.jointMass e u d

private theorem binaryEvent_measurable {Ω : Type*} [MeasurableSpace Ω]
    {T : Set Ω} (hT : MeasurableSet T) (e : Bool) : MeasurableSet (binaryEvent T e) := by
  cases e <;> simp only [binaryEvent, Bool.false_eq_true, ↓reduceIte]
  · exact hT.compl
  · exact hT

private theorem measureReal_binary_split {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.real A = μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) := by
  have hUnion : (A ∩ B) ∪ (A ∩ Bᶜ) = A := by
    ext ω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have hDisjoint : Disjoint (A ∩ B) (A ∩ Bᶜ) :=
    Set.disjoint_left.2 fun _ h₁ h₂ => h₂.2 h₁.2
  simpa only [hUnion] using measureReal_union hDisjoint (hA.inter hB.compl)

private theorem measureReal_cell {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (e : Bool) (u : Fin (n + 1)) :
    μ.real (binaryEvent T e ∩ U ⁻¹' {u}) = m.armProb e * m.mass e u := by
  rw [measureReal_binary_split ((binaryEvent_measurable hT e).inter
    (hU (measurableSet_singleton u))) hD]
  change μ.real (binaryEvent T e ∩ U ⁻¹' {u} ∩ binaryEvent D true) +
    μ.real (binaryEvent T e ∩ U ⁻¹' {u} ∩ binaryEvent D false) = _
  rw [hLaw, hLaw, m.jointMass_sum_outcome]

private theorem measureReal_eq_sum_cells {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {U : Ω → ι} (hU : Measurable U)
    {A : Set Ω} (hA : MeasurableSet A) :
    μ.real A = ∑ u, μ.real (A ∩ U ⁻¹' {u}) := by
  have hUnion : (⋃ u, A ∩ U ⁻¹' {u}) = A := by ext ω; simp
  have hDisjoint : Pairwise (Function.onFun Disjoint fun u => A ∩ U ⁻¹' {u}) :=
    fun u v huv => Set.disjoint_left.2 fun _ h₁ h₂ => huv (h₁.2.symm.trans h₂.2)
  simpa only [hUnion] using measureReal_iUnion_fintype hDisjoint
    (fun u => hA.inter (hU (measurableSet_singleton u)))

private theorem armProb_pos {n : ℕ} (m : FiniteRiskModel n) (e : Bool) :
    0 < m.armProb e := by
  cases e
  · exact sub_pos.mpr m.exposureProb_mem.2
  · exact m.exposureProb_mem.1

private theorem cond_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Set Ω} (hA : MeasurableSet A) (B : Set Ω) :
    (μ[|A]).real B = (μ.real A)⁻¹ * μ.real (A ∩ B) := by
  simp only [Measure.real, cond_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- The marginal mixture agrees with the measured confounder law. -/
theorem marginalMass_eq_measureReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (u : Fin (n + 1)) :
    m.marginalMass u = μ.real (U ⁻¹' {u}) := by
  have hA := hU (measurableSet_singleton u)
  have hSplit := measureReal_binary_split (μ := μ) hA hT
  rw [Set.inter_comm (U ⁻¹' {u}) T, Set.inter_comm (U ⁻¹' {u}) Tᶜ] at hSplit
  change μ.real (U ⁻¹' {u}) = μ.real (binaryEvent T true ∩ U ⁻¹' {u}) +
    μ.real (binaryEvent T false ∩ U ⁻¹' {u}) at hSplit
  rw [measureReal_cell hT hD hU hLaw, measureReal_cell hT hD hU hLaw] at hSplit
  exact hSplit.symm

/-- Each model arm has the stated exposure probability. -/
theorem armProb_eq_measureReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (e : Bool) :
    m.armProb e = μ.real (binaryEvent T e) := by
  rw [measureReal_eq_sum_cells hU (binaryEvent_measurable hT e)]
  simp only [measureReal_cell hT hD hU hLaw, ← Finset.mul_sum]
  rw [show ∑ u, m.mass e u = 1 from (m.confounderLaw e).total_of_fintype, mul_one]

/-- Conditional confounder probabilities in the two exposure arms. -/
theorem mass_eq_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (e : Bool) (u : Fin (n + 1)) :
    m.mass e u = (μ[|binaryEvent T e]).real (U ⁻¹' {u}) := by
  rw [cond_real μ (binaryEvent_measurable hT e),
    ← armProb_eq_measureReal hT hD hU hLaw, measureReal_cell hT hD hU hLaw,
    ← mul_assoc, inv_mul_cancel₀ (armProb_pos m e).ne', one_mul]

/-- On a positive cell the kernel value agrees with ordinary conditioning. -/
theorem risk_eq_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (e : Bool) (u : Fin (n + 1))
    (hu : 0 < m.mass e u) :
    m.risk e u = (μ[|binaryEvent T e ∩ U ⁻¹' {u}]).real D := by
  rw [cond_real μ ((binaryEvent_measurable hT e).inter
    (hU (measurableSet_singleton u))), measureReal_cell hT hD hU hLaw]
  have hAtom := hLaw e u true
  change μ.real (binaryEvent T e ∩ U ⁻¹' {u} ∩ D) =
    m.armProb e * m.mass e u * m.risk e u at hAtom
  rw [hAtom, ← mul_assoc, inv_mul_cancel₀ (mul_pos (armProb_pos m e) hu).ne', one_mul]

/-- Total probability for observed risk in an exposure arm. -/
theorem observedRisk_eq_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (e : Bool) :
    m.observedRisk e = (μ[|binaryEvent T e]).real D := by
  rw [cond_real μ (binaryEvent_measurable hT e),
    ← armProb_eq_measureReal hT hD hU hLaw,
    measureReal_eq_sum_cells hU ((binaryEvent_measurable hT e).inter hD)]
  have hAtom (u : Fin (n + 1)) :
      μ.real (binaryEvent T e ∩ D ∩ U ⁻¹' {u}) =
        m.armProb e * (m.risk e u * m.mass e u) := by
    have hSet : binaryEvent T e ∩ D ∩ U ⁻¹' {u} =
        binaryEvent T e ∩ U ⁻¹' {u} ∩ binaryEvent D true := by
      simp only [binaryEvent, ↓reduceIte]
      ext ω
      simp only [Set.mem_inter_iff]
      tauto
    rw [hSet, hLaw]
    simp only [jointMass, ↓reduceIte]
    ring
  simp only [hAtom]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ (armProb_pos m e).ne', one_mul]
  rfl

/-- The observed risk ratio agrees with the ratio of observed event probabilities. -/
theorem observedRR_eq_cond_ratio {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) :
    m.observedRR = (μ[|T]).real D / (μ[|Tᶜ]).real D := by
  simpa only [observedRR, binaryEvent, Bool.false_eq_true, ↓reduceIte] using
    congrArg₂ (fun a b : ℝ => a / b) (observedRisk_eq_cond hT hD hU hLaw true)
      (observedRisk_eq_cond hT hD hU hLaw false)

/-- Standardized risk uses the joint law on positive cells and the supplied
version of the risk kernel on null cells. -/
theorem standardizedRisk_eq_sum_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T D : Set Ω} {U : Ω → Fin (n + 1)} (hT : MeasurableSet T) (hD : MeasurableSet D)
    (hU : Measurable U) (hLaw : m.HasJointLaw μ T D U) (e : Bool) :
    m.standardizedRisk e = ∑ u, μ.real (U ⁻¹' {u}) *
      (if μ (binaryEvent T e ∩ U ⁻¹' {u}) = 0 then m.risk e u
       else (μ[|binaryEvent T e ∩ U ⁻¹' {u}]).real D) := by
  classical
  unfold standardizedRisk
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [marginalMass_eq_measureReal hT hD hU hLaw]
  by_cases hz : μ (binaryEvent T e ∩ U ⁻¹' {u}) = 0
  · simp only [hz, ↓reduceIte, mul_comm]
  · have hm : m.mass e u ≠ 0 := by
      intro hm
      have hCell := measureReal_cell hT hD hU hLaw e u
      rw [hm, mul_zero] at hCell
      exact hz ((measureReal_eq_zero_iff).1 hCell)
    rw [ite_eq_right hz, ← risk_eq_cond hT hD hU hLaw e u
      (lt_of_le_of_ne ((m.confounderLaw e).weights_nonneg u) (Ne.symm hm)), mul_comm]

private theorem binary_eq_indicator {Ω : Type*} (Y : Ω → ℝ)
    (hY : ∀ ω, Y ω = 0 ∨ Y ω = 1) :
    Y = (Y ⁻¹' {1}).indicator (fun _ => (1 : ℝ)) := by
  classical
  funext ω
  rcases hY ω with h | h <;> simp [Set.indicator, h]

private theorem integral_binary {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Y : Ω → ℝ} (hY : Measurable Y) (hBinary : ∀ ω, Y ω = 0 ∨ Y ω = 1) :
    ∫ ω, Y ω ∂μ = μ.real (Y ⁻¹' {1}) := by
  calc
    ∫ ω, Y ω ∂μ = ∫ ω, (Y ⁻¹' {1}).indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) (binary_eq_indicator Y hBinary)
    _ = μ.real (Y ⁻¹' {1}) := by
      simpa only [smul_eq_mul, mul_one] using
        integral_indicator_const (1 : ℝ) (hY (measurableSet_singleton 1))

private theorem integrable_binary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hBinary : ∀ ω, Y ω = 0 ∨ Y ω = 1) : Integrable Y μ := by
  exact (binary_eq_indicator Y hBinary).symm ▸
    (integrable_const (1 : ℝ)).indicator (hY (measurableSet_singleton 1))

/-- Under consistency and strong ignorability the population-standardized
risk ratio is the ratio of the two potential outcome risks. -/
theorem standardizedRR_eq_causalRR {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T : Set Ω} {U : Ω → Fin (n + 1)} {Y₀ Y₁ : Ω → ℝ}
    (hT : MeasurableSet T) (hU : Measurable U) (hY₀ : Measurable Y₀)
    (hY₁ : Measurable Y₁) (h₀ : ∀ ω, Y₀ ω = 0 ∨ Y₀ ω = 1)
    (h₁ : ∀ ω, Y₁ ω = 0 ∨ Y₁ ω = 1)
    (hIgn : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) U)
    (hLaw : m.HasJointLaw μ T (observed T Y₀ Y₁ ⁻¹' {1}) U) :
    m.standardizedRR = μ.real (Y₁ ⁻¹' {1}) / μ.real (Y₀ ⁻¹' {1}) := by
  classical
  have hObserved : Measurable (observed T Y₀ Y₁) :=
    (hY₁.indicator hT).add (hY₀.indicator hT.compl)
  have hBinary : ∀ ω, observed T Y₀ Y₁ ω = 0 ∨ observed T Y₀ Y₁ ω = 1 := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [observed_eq_on_treated T Y₀ Y₁ hω]
      exact h₁ ω
    · rw [observed_eq_on_control T Y₀ Y₁ hω]
      exact h₀ ω
  have hD := hObserved (measurableSet_singleton 1)
  have hCell (e : Bool) (u : Fin (n + 1)) : μ (binaryEvent T e ∩ U ⁻¹' {u}) ≠ 0 := by
    have hA : 0 < μ.real (U ⁻¹' {u}) := by
      rw [← marginalMass_eq_measureReal hT hD hU hLaw]
      exact m.marginalMass_pos u
    have hμA : μ (U ⁻¹' {u}) ≠ 0 := fun hz =>
      hA.ne' ((measureReal_eq_zero_iff).2 hz)
    obtain ⟨hpos, hlt⟩ := hIgn.2 u hμA
    have hTCell := measureReal_inter_preimage_eq_propensity_mul (μ := μ) (T := T) (X := U) u
    have hPositive : 0 < μ.real (binaryEvent T e ∩ U ⁻¹' {u}) := by
      cases e
      · have hSplit := measureReal_binary_split (μ := μ)
          (hU (measurableSet_singleton u)) hT
        rw [Set.inter_comm (U ⁻¹' {u}) T,
          Set.inter_comm (U ⁻¹' {u}) Tᶜ, hTCell] at hSplit
        have hComplement : μ.real (Tᶜ ∩ U ⁻¹' {u}) =
            (1 - propensity μ T U u) * μ.real (U ⁻¹' {u}) := by
          linear_combination -hSplit
        change 0 < μ.real (Tᶜ ∩ U ⁻¹' {u})
        rw [hComplement]
        exact mul_pos (sub_pos.mpr hlt) hA
      · change 0 < μ.real (T ∩ U ⁻¹' {u})
        rw [hTCell]
        exact mul_pos hpos hA
    exact fun hz => hPositive.ne' ((measureReal_eq_zero_iff).2 hz)
  have hRisk (e : Bool) : m.standardizedRisk e =
      ∑ u, μ.real (U ⁻¹' {u}) *
        ∫ ω, observed T Y₀ Y₁ ω ∂μ[|binaryEvent T e ∩ U ⁻¹' {u}] := by
    rw [standardizedRisk_eq_sum_cond hT hD hU hLaw]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [ite_eq_right (hCell e u), integral_binary _ hObserved hBinary]
  have hTreated := integral_eq_sum_standardized_treated (Y₀ := Y₀)
    hT hU hY₁ (integrable_binary hY₁ h₁) (hIgn.comp measurable_snd)
  have hControl := integral_eq_sum_standardized_control (Y₁ := Y₁)
    hT hU hY₀ (integrable_binary hY₀ h₀) (hIgn.comp measurable_fst)
  rw [standardizedRR, hRisk true, hRisk false]
  change (∑ u, μ.real (U ⁻¹' {u}) * ∫ ω, observed T Y₀ Y₁ ω ∂μ[|T ∩ U ⁻¹' {u}]) /
    (∑ u, μ.real (U ⁻¹' {u}) * ∫ ω, observed T Y₀ Y₁ ω ∂μ[|Tᶜ ∩ U ⁻¹' {u}]) = _
  rw [← hTreated, ← hControl, integral_binary μ hY₁ h₁, integral_binary μ hY₀ h₀]

/-- The risk-ratio bound applied to binary potential outcomes under consistency
and strong ignorability. -/
theorem confounding_causalRR_le_boundingFactor {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {m : FiniteRiskModel n}
    {T : Set Ω} {U : Ω → Fin (n + 1)} {Y₀ Y₁ : Ω → ℝ}
    (hT : MeasurableSet T) (hU : Measurable U) (hY₀ : Measurable Y₀)
    (hY₁ : Measurable Y₁) (h₀ : ∀ ω, Y₀ ω = 0 ∨ Y₀ ω = 1)
    (h₁ : ∀ ω, Y₁ ω = 0 ∨ Y₁ ω = 1)
    (hIgn : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) U)
    (hLaw : m.HasJointLaw μ T (observed T Y₀ Y₁ ⁻¹' {1}) U) :
    m.observedRR / (μ.real (Y₁ ⁻¹' {1}) / μ.real (Y₀ ⁻¹' {1})) ≤
      confoundingBoundingFactor m.exposureConfounderRR m.confounderOutcomeRR := by
  rw [← standardizedRR_eq_causalRR hT hU hY₀ hY₁ h₀ h₁ hIgn hLaw]
  exact m.confoundingRR_le_boundingFactor

/-- Standardize to a finite population of measured strata. Each stratum first
standardizes both arms to its own confounder law. -/
noncomputable def strataStandardizedRR {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (w : Convexity.StdSimplex ℝ ι) (m : (c : ι) → FiniteRiskModel (n c)) : ℝ :=
  (∑ c, w.weights c * (m c).standardizedRisk true) /
    ∑ c, w.weights c * (m c).standardizedRisk false

private theorem weighted_sum_pos {ι : Type*} [Fintype ι]
    (w : Convexity.StdSimplex ℝ ι) (r : ι → ℝ) (hr : ∀ c, 0 < r c) :
    0 < ∑ c, w.weights c * r c := by
  apply Finset.sum_pos'
  · exact fun c _ => mul_nonneg (w.weights_nonneg c) (hr c).le
  · have hw : ∃ c, 0 < w.weights c := by
      by_contra! h
      have hz (c : ι) : w.weights c = 0 := le_antisymm (h c) (w.weights_nonneg c)
      have ht := w.total_of_fintype
      simp [hz] at ht
    obtain ⟨c, hc⟩ := hw
    exact ⟨c, Finset.mem_univ _, mul_pos hc (hr c)⟩

/-- The aggregate ratio is bounded below by the least corrected stratum ratio. -/
theorem strataStandardizedRR_ge_min {ι : Type*} [Fintype ι] [Nonempty ι] {n : ι → ℕ}
    (w : Convexity.StdSimplex ℝ ι) (m : (c : ι) → FiniteRiskModel (n c)) :
    Finset.univ.inf' Finset.univ_nonempty (fun c =>
      (m c).observedRR /
        confoundingBoundingFactor (m c).exposureConfounderRR (m c).confounderOutcomeRR) ≤
      strataStandardizedRR w m := by
  let r : ι → ℝ := fun c => (m c).observedRR /
    confoundingBoundingFactor (m c).exposureConfounderRR (m c).confounderOutcomeRR
  let α := Finset.univ.inf' Finset.univ_nonempty r
  have hArm (c : ι) : α * (m c).standardizedRisk false ≤ (m c).standardizedRisk true := by
    have hc : α ≤ (m c).standardizedRR :=
      (Finset.inf'_le r (Finset.mem_univ c)).trans
        (m c).observedRR_div_boundingFactor_le_standardizedRR
    exact (le_div_iff₀ ((m c).standardizedRisk_pos false)).mp hc
  apply (le_div_iff₀ (weighted_sum_pos w (fun c => (m c).standardizedRisk false)
    (fun c => (m c).standardizedRisk_pos false))).mpr
  change α * (∑ c, w.weights c * (m c).standardizedRisk false) ≤ _
  calc
    α * (∑ c, w.weights c * (m c).standardizedRisk false) =
        ∑ c, w.weights c * (α * (m c).standardizedRisk false) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ c, w.weights c * (m c).standardizedRisk true :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hArm c) (w.weights_nonneg c)

/-- If the standardized effect is common across strata, the aggregate ratio
is bounded below by the greatest corrected stratum ratio. -/
theorem strataStandardizedRR_ge_max_of_common {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ι → ℕ} (w : Convexity.StdSimplex ℝ ι) (m : (c : ι) → FiniteRiskModel (n c))
    {β : ℝ} (hCommon : ∀ c, (m c).standardizedRR = β) :
    Finset.univ.sup' Finset.univ_nonempty (fun c =>
      (m c).observedRR /
        confoundingBoundingFactor (m c).exposureConfounderRR (m c).confounderOutcomeRR) ≤
      strataStandardizedRR w m := by
  have hArm (c : ι) : (m c).standardizedRisk true = β * (m c).standardizedRisk false :=
    (div_eq_iff ((m c).standardizedRisk_pos false).ne').mp (hCommon c)
  have hSum : (∑ c, w.weights c * (m c).standardizedRisk true) =
      β * ∑ c, w.weights c * (m c).standardizedRisk false := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hArm c]
    ring
  have hAggregate : strataStandardizedRR w m = β := by
    unfold strataStandardizedRR
    rw [hSum, mul_div_cancel_right₀ _
      (weighted_sum_pos w (fun c => (m c).standardizedRisk false)
        (fun c => (m c).standardizedRisk_pos false)).ne']
  rw [hAggregate]
  exact Finset.sup'_le Finset.univ_nonempty _ fun c _ =>
    (m c).observedRR_div_boundingFactor_le_standardizedRR.trans (le_of_eq (hCommon c))

end FiniteRiskModel

end MathlibExt.Probability.Causality
