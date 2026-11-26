/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Basic

import Mathlib.Data.Finset.Max
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The single-threshold prophet inequality -/

open MeasureTheory Set

namespace ProbabilityTheory

private def reach {ι Ω : Type*} [LT ι] (X : ι → Ω → ℝ) (A : Set ℝ) (i : ι) : Set Ω :=
  {ω | ∀ j, j < i → X j ω ∉ A}

private def firstAccept {ι Ω : Type*} [LT ι] (X : ι → Ω → ℝ) (A : Set ℝ) (i : ι) : Set Ω :=
  reach X A i ∩ X i ⁻¹' A

private theorem measurableSet_reach {ι Ω : Type*} [LinearOrder ι] [Countable ι]
    [MeasurableSpace Ω] {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    {A : Set ℝ} (hA : MeasurableSet A) (i : ι) : MeasurableSet (reach X A i) := by
  have h : reach X A i = ⋂ j : {j : ι // j < i}, (X j ⁻¹' A)ᶜ := by
    ext ω
    simp [reach]
  rw [h]
  exact MeasurableSet.iInter fun j => (hX j hA).compl

private theorem integral_reach_mul {ι Ω : Type*} [LinearOrder ι] [Countable ι]
    [MeasurableSpace Ω] {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    {A : Set ℝ} (hA : MeasurableSet A) (i : ι) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, (reach X A i).indicator (g ∘ X i) ω ∂μ =
      μ.real (reach X A i) * ∫ ω, g (X i ω) ∂μ := by
  let L : Set ι := {j | j < i}
  let R : Set ι := {i}
  have hdis : Disjoint L R := by
    refine Set.disjoint_left.mpr fun j hj hk => ?_
    have he : j = i := hk
    have hlt : j < i := hj
    rw [he] at hlt
    exact (lt_irrefl i) hlt
  let f : (L → ℝ) → ℝ :=
    (⋂ j : L, (Function.eval j ⁻¹' A)ᶜ).indicator 1
  let k : (R → ℝ) → ℝ := fun z => g (z ⟨i, rfl⟩)
  have hf : Measurable f := measurable_const.indicator
    (MeasurableSet.iInter fun j => ((measurable_pi_apply j) hA).compl)
  have hk : Measurable k := hg.comp (measurable_pi_apply _)
  have hi := (hind.indepFun_set L R hdis hX).comp hf hk
  have hleft : f ∘ (fun ω (j : L) => X j ω) = (reach X A i).indicator (1 : Ω → ℝ) := by
    funext ω
    have he : (fun j : L => X j ω) ∈ ⋂ j : L, (Function.eval j ⁻¹' A)ᶜ ↔
        ω ∈ reach X A i := by simp [L, reach]
    change (⋂ j : L, (Function.eval j ⁻¹' A)ᶜ).indicator (1 : (L → ℝ) → ℝ)
        (fun j : L => X j ω) = (reach X A i).indicator (1 : Ω → ℝ) ω
    by_cases h : ω ∈ reach X A i
    · rw [indicator_of_mem (he.mpr h), indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (fun hh => h (he.mp hh)), indicator_of_notMem h]
  have hright : k ∘ (fun ω (j : R) => X j ω) = g ∘ X i := rfl
  rw [hleft, hright] at hi
  have h := hi.integral_fun_mul_eq_mul_integral
    ((measurable_const.indicator (measurableSet_reach hX hA i)).aestronglyMeasurable)
    ((hg.comp (hX i)).aestronglyMeasurable)
  rw [integral_indicator_one (measurableSet_reach hX hA i)] at h
  change (∫ ω, (reach X A i).indicator (g ∘ X i) ω ∂μ) =
    μ.real (reach X A i) * ∫ ω, (g ∘ X i) ω ∂μ
  rw [← h]
  congr with ω
  by_cases hω : ω ∈ reach X A i <;> simp [hω]

private theorem firstAccept_decomposition {ι Ω : Type*} [LinearOrder ι] [Fintype ι]
    (X : ι → Ω → ℝ) (p : ℝ) (A : Set ℝ) (hlo : Ioi p ⊆ A) (hhi : A ⊆ Ici p)
    (ω : Ω) :
    (∑ i, (firstAccept X A i).indicator (X i) ω) =
      {ω | ∃ i, X i ω ∈ A}.indicator (fun _ => p) ω +
        ∑ i, (reach X A i).indicator (fun ω => max (X i ω - p) 0) ω := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => X i ω ∈ A)
  have ha (i : ι) : i ∈ s ↔ X i ω ∈ A := by simp [s]
  by_cases h : s.Nonempty
  · let j := s.min' h
    have hj : X j ω ∈ A := (ha j).mp (s.min'_mem h)
    have hreach : ω ∈ reach X A j := by
      intro i hi hAi
      exact (not_le_of_gt hi) (s.min'_le i ((ha i).mpr hAi))
    have hstop : ω ∈ firstAccept X A j := ⟨hreach, hj⟩
    have hother : ∀ i, i ≠ j → ω ∉ firstAccept X A i := by
      intro i hne hi
      have hle : j ≤ i := s.min'_le i ((ha i).mpr hi.2)
      exact hi.1 j (lt_of_le_of_ne hle (fun he => hne he.symm)) hj
    have hotherG : ∀ i, i ≠ j →
        (reach X A i).indicator (fun ω => max (X i ω - p) 0) ω = 0 := by
      intro i hne
      by_cases hi : ω ∈ reach X A i
      · have hAi : X i ω ∉ A := fun hAi => hother i hne ⟨hi, hAi⟩
        have hle : X i ω ≤ p := le_of_not_gt fun hgt => hAi (hlo hgt)
        rw [indicator_of_mem hi, max_eq_right (sub_nonpos.mpr hle)]
      · exact indicator_of_notMem hi _
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun i _ hi =>
      indicator_of_notMem (hother i hi) _), indicator_of_mem hstop,
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun i _ hi => hotherG i hi),
      indicator_of_mem hreach, indicator_of_mem (show ∃ i, X i ω ∈ A from ⟨j, hj⟩),
      max_eq_left (sub_nonneg.mpr (hhi hj))]
    ring
  · have hno (i : ι) : X i ω ∉ A := fun hi => h ⟨i, (ha i).mpr hi⟩
    have hleft (i : ι) : (firstAccept X A i).indicator (X i) ω = 0 :=
      indicator_of_notMem (fun hi : ω ∈ firstAccept X A i => hno i hi.2) _
    have hright (i : ι) : (reach X A i).indicator (fun ω => max (X i ω - p) 0) ω = 0 := by
      have hle : X i ω ≤ p := le_of_not_gt fun hgt => hno i (hlo hgt)
      simp [max_eq_right (sub_nonpos.mpr hle)]
    simp [hleft, hright, show ¬∃ i, X i ω ∈ A from fun ⟨i, hi⟩ => hno i hi]

/-- The payoff from accepting the first observation in `A` in the given order of the indices.
The sum has at most one nonzero term, and the payoff is zero if there is no accepted value. -/
@[expose] public noncomputable def singleThresholdReward {ι Ω : Type*}
    [LinearOrder ι] [Fintype ι] (X : ι → Ω → ℝ) (A : Set ℝ) (ω : Ω) : ℝ := by
  classical
  exact ∑ i, {η | X i η ∈ A ∧ ∀ j, j < i → X j η ∉ A}.indicator (X i) ω

private theorem singleThresholdReward_eq_sum {ι Ω : Type*} [LinearOrder ι] [Fintype ι]
    (X : ι → Ω → ℝ) (A : Set ℝ) (ω : Ω) :
    singleThresholdReward X A ω = ∑ i, (firstAccept X A i).indicator (X i) ω := by
  classical
  unfold singleThresholdReward
  congr 1
  funext i
  congr 1
  ext η
  exact and_comm

private theorem measurable_sup'_univ {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) := by
  apply measurable_of_Iic
  intro t
  have h : (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)) ⁻¹' Iic t =
      ⋂ i, X i ⁻¹' Iic t := by
    ext ω
    simp [Finset.sup'_le_iff]
  rw [h]
  exact MeasurableSet.iInter fun i => hX i measurableSet_Iic

/-- **Prophet inequality with a single threshold.** For independent, nonnegative, integrable
observations, set `p` to one half of the expected maximum. The expected payoff from accepting
the first observation in `A` is at least `p` whenever `A` is measurable and lies between
`(p, ∞)` and `[p, ∞)`. In particular, the same bound holds for both decisions on a tie.
See B. Lucier, *An economic view of prophet inequalities*, Theorem 3.1. -/
public theorem single_threshold_prophet_inequality {ι Ω : Type*} [LinearOrder ι] [Fintype ι]
    [Nonempty ι] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ) (hpos : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω)
    (hind : iIndepFun X μ) :
    let p := (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ) / 2
    ∀ A : Set ℝ, MeasurableSet A → Ioi p ⊆ A → A ⊆ Ici p →
      p ≤ ∫ ω, singleThresholdReward X A ω ∂μ := by
  classical
  intro p A hA hlo hhi
  let V (ω : Ω) := Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)
  let G (i : ι) (ω : Ω) := max (X i ω - p) 0
  let B : Set Ω := {ω | ∃ i, X i ω ∈ A}
  have hBm : MeasurableSet B := by
    have hB : B = ⋃ i, X i ⁻¹' A := by ext; simp [B]
    rw [hB]
    exact MeasurableSet.iUnion fun i => hX i hA
  have hV : Measurable V := measurable_sup'_univ hX
  have hVi : Integrable V μ := by
    refine (integrable_finsetSum Finset.univ (fun i _ => hint i)).mono_nonneg
      hV.aestronglyMeasurable ?_ ?_
    · filter_upwards [hpos] with ω hω
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
      rw [show V ω = X i ω from hi]
      exact hω i
    · filter_upwards [hpos] with ω hω
      obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
      change V ω ≤ ∑ j, X j ω
      rw [show V ω = X i ω from he]
      exact Finset.single_le_sum (fun j _ => hω j) hi
  have hGi (i : ι) : Integrable (G i) μ := by
    exact ((hint i).sub (integrable_const p)).sup (integrable_const 0)
  have hG0 (i : ι) : 0 ≤ ∫ ω, G i ω ∂μ :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hsum : p ≤ ∑ i, ∫ ω, G i ω ∂μ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hGi i)]
    have hle : (∫ ω, V ω - p ∂μ) ≤ ∫ ω, ∑ i, G i ω ∂μ := by
      refine integral_mono (hVi.sub (integrable_const p))
        (integrable_finsetSum Finset.univ (fun i _ => hGi i)) (fun ω => ?_)
      obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
      change V ω - p ≤ ∑ i, G i ω
      rw [show V ω = X i ω from he]
      have hGi_le : G i ω ≤ ∑ j, G j ω :=
        Finset.single_le_sum (f := fun j => G j ω) (fun _ _ => le_max_right _ _) hi
      exact (le_max_left (X i ω - p) 0).trans hGi_le
    rw [integral_sub hVi (integrable_const p), integral_const, probReal_univ, one_smul] at hle
    have hp : (∫ ω, V ω ∂μ) = 2 * p := by
      change (∫ ω, V ω ∂μ) = 2 * ((∫ ω, V ω ∂μ) / 2)
      ring
    linarith
  have hweight (i : ι) : μ.real Bᶜ ≤ μ.real (reach X A i) :=
    measureReal_mono fun ω hω _ _ hj => hω ⟨_, hj⟩
  have hbudget : μ.real Bᶜ * p ≤
      ∑ i, μ.real (reach X A i) * ∫ ω, G i ω ∂μ := by
    calc
      _ ≤ μ.real Bᶜ * ∑ i, ∫ ω, G i ω ∂μ :=
        mul_le_mul_of_nonneg_left hsum measureReal_nonneg
      _ = ∑ i, μ.real Bᶜ * ∫ ω, G i ω ∂μ := Finset.mul_sum ..
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hweight i) (hG0 i)
  have hdecomp : (fun ω => singleThresholdReward X A ω) =
      fun ω => B.indicator (fun _ => p) ω +
        ∑ i, (reach X A i).indicator (G i) ω := by
    funext ω
    rw [singleThresholdReward_eq_sum, firstAccept_decomposition X p A hlo hhi]
  have hsurplus (i : ι) : Integrable ((reach X A i).indicator (G i)) μ :=
    (hGi i).indicator (measurableSet_reach hX hA i)
  have hfactor (i : ι) : ∫ ω, (reach X A i).indicator (G i) ω ∂μ =
      μ.real (reach X A i) * ∫ ω, G i ω ∂μ :=
    integral_reach_mul hX hind hA i
      ((measurable_id.sub measurable_const).max measurable_const)
  rw [hdecomp, integral_add ((integrable_const p).indicator hBm)
      (integrable_finsetSum Finset.univ (fun i _ => hsurplus i)),
    integral_indicator_const p hBm, smul_eq_mul,
    integral_finsetSum Finset.univ (fun i _ => hsurplus i)]
  simp_rw [hfactor]
  calc
    p = μ.real B * p + μ.real Bᶜ * p := by
      rw [← add_mul, measureReal_add_measureReal_compl hBm, probReal_univ, one_mul]
    _ ≤ _ := add_le_add (le_refl _) hbudget

/-- **The factor one half is sharp in the prophet inequality.** The first prize is one.
The second is zero except with probability `ε`, when it is `1/ε`. The expected maximum is
`2 - ε`. A first decision `d₁` depends only on the first prize, and a second decision `d₂`
may see both prizes. Every such policy has expected payoff at most one. See the two-chest
example in B. Lucier, *An economic view of prophet inequalities*, §2. -/
public theorem single_threshold_prophet_two_prize_sharpness (ε : Set.Icc (0 : ℝ) 1)
    (hε : 0 < (ε : ℝ)) :
    let μ := bernoulliMeasure ((ε : ℝ)⁻¹) 0 ε
    (∫ x, max (1 : ℝ) x ∂μ) = 2 - (ε : ℝ) ∧
    ∀ (d₁ : ℝ → Bool) (d₂ : ℝ → ℝ → Bool),
      (∫ x, if d₁ 1 then (1 : ℝ) else if d₂ 1 x then x else 0 ∂μ) ≤ 1 := by
  intro μ
  have hεinv : (1 : ℝ) ≤ (ε : ℝ)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hε, one_mul]
    exact ε.2.2
  have hmul : (ε : ℝ) * (ε : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  constructor
  · rw [show μ = bernoulliMeasure ((ε : ℝ)⁻¹) 0 ε from rfl, integral_bernoulliMeasure]
    simp only [smul_eq_mul, max_eq_right hεinv, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1), hmul,
      mul_one]
    ring
  · intro d₁ d₂
    rw [show μ = bernoulliMeasure ((ε : ℝ)⁻¹) 0 ε from rfl, integral_bernoulliMeasure]
    cases d₁ 1
    · cases d₂ 1 ((ε : ℝ)⁻¹)
      · simp
      · simp [smul_eq_mul, hmul]
    · simp [smul_eq_mul]

end ProbabilityTheory
