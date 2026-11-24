/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Decision.Risk.Countable
public import MathlibExt.Probability.Decision.BinaryCostAdapter
public import Mathlib.Probability.Decision.BayesEstimator
public import Mathlib.Probability.Kernel.Basic

/-!
# Weighted-score Bayes rule for finite binary decisions

For densities `P0, P1` on a finite observation space, prior weight `π`,
and costs `cFP, cFN`, the weighted scores at `x` are
`S1 x = (1 - π) * cFP * P0 x` (cost of deciding `true`) and
`S0 x = π * cFN * P1 x` (cost of deciding `false`). No division is formed
anywhere: in particular no likelihood ratio and no posterior odds.

The deterministic rule that decides by the strict weighted-score
comparison is a Bayes estimator, by the existing expected-loss argmin
optimality theorem. A randomized rule following the strict comparisons
minimizes the real risk over every randomized competitor. Randomization
is free exactly at genuine weighted ties
`π * cFN * P1 x = (1 - π) * cFP * P0 x`, which include joint-zero support;
one-sided support `P0 x = 0 < P1 x` strictly favors `true`. Equal densities
alone are not a tie under unequal priors or costs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MathlibExt.Probability.Decision

/-- Per-observation real contribution of randomization level `a` at `x`:
`a * S1 x + (1 - a) * S0 x`. -/
def weightedScoreContribution {𝒳 : Type*} (P0 P1 : 𝒳 → ℝ) (π cFP cFN a : ℝ) (x : 𝒳) : ℝ :=
  a * ((1 - π) * cFP * P0 x) + (1 - a) * (π * cFN * P1 x)

private theorem isProbabilityMeasure_dirac_sum {𝒳 : Type*} [MeasurableSpace 𝒳]
    [Fintype 𝒳] (P : 𝒳 → ℝ) (hP : ∀ x, 0 ≤ P x) (hPsum : ∑ x, P x = 1) :
    IsProbabilityMeasure (∑ x, ENNReal.ofReal (P x) • Measure.dirac x) := by
  refine ⟨?_⟩
  have hterm : ∀ x : 𝒳, (ENNReal.ofReal (P x) • Measure.dirac x) Set.univ
      = ENNReal.ofReal (P x) := by
    intro x
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ x), smul_eq_mul,
      mul_one]
  have hsum : (∑ x, ENNReal.ofReal (P x) • Measure.dirac x) Set.univ
      = ∑ x, ENNReal.ofReal (P x) := by
    rw [Measure.finsetSum_apply]
    exact Finset.sum_congr rfl (fun x _ => hterm x)
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => hP x), hPsum, ENNReal.ofReal_one]

private theorem count_withDensity_eq_dirac_sum {𝒳 : Type*} [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] [Fintype 𝒳] (P : 𝒳 → ℝ) :
    Measure.count.withDensity (fun x => ENNReal.ofReal (P x))
      = ∑ x, ENNReal.ofReal (P x) • Measure.dirac x := by
  rw [Measure.ext_iff_singleton]
  intro a
  have hres : Measure.count.restrict {a} = Measure.dirac a := by
    ext s hs
    rw [Measure.restrict_apply hs]
    by_cases ha : a ∈ s
    · rw [Set.inter_singleton_of_mem ha]
      simp [Measure.count_apply (measurableSet_singleton a), Set.encard_singleton,
        Measure.dirac_apply, Set.indicator_of_mem ha]
    · rw [Set.inter_singleton_of_notMem ha]
      simp [Measure.count_apply MeasurableSet.empty, Set.encard_empty,
        Measure.dirac_apply, Set.indicator_of_notMem ha]
  rw [withDensity_apply _ (measurableSet_singleton a), hres, lintegral_dirac,
    Measure.finsetSum_apply Finset.univ _ _,
    Finset.sum_eq_single a
      (fun x _ hxa => by
        rw [Measure.smul_apply, Measure.dirac_apply _ _,
          Set.indicator_of_notMem (by simpa using hxa) _, smul_zero])
      (fun h => absurd (Finset.mem_univ a) h),
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton a), smul_eq_mul,
    mul_one]

private theorem weightedScore_bayesRule_exists_aux
    {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [Fintype 𝒳]
    (P0 P1 : 𝒳 → ℝ) (π cFP cFN : ℝ)
    (hP0 : ∀ x, 0 ≤ P0 x) (hP0sum : ∑ x, P0 x = 1)
    (hP1 : ∀ x, 0 ≤ P1 x) (hP1sum : ∑ x, P1 x = 1)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hcFP : 0 < cFP) (hcFN : 0 < cFN) :
    (∃ f : 𝒳 → Bool, ∃ hf : Measurable f,
      (∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x → f x = true)
      ∧ (∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x → f x = false)
      ∧ IsBayesEstimator
          (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
          (Kernel.deterministic f hf)
          (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true)) := by
  have hP0m : Measurable P0 := measurable_of_finite _
  have hP1m : Measurable P1 := measurable_of_finite _
  have hprob0 : IsProbabilityMeasure (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x) :=
    isProbabilityMeasure_dirac_sum P0 hP0 hP0sum
  have hprob1 : IsProbabilityMeasure (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x) :=
    isProbabilityMeasure_dirac_sum P1 hP1 hP1sum
  obtain ⟨hf, hbayes⟩ := @BinaryCostAdapter.isBayesEstimator_binaryCostRule _ _
    Measure.count _ _ hprob0 hprob1 P0 P1 hP0m hP1m hP0 hP1
    (count_withDensity_eq_dirac_sum P0).symm (count_withDensity_eq_dirac_sum P1).symm
    (1 - π) π (sub_pos.mpr hπ1) hπ0 (by ring) 0 cFN cFP 0 hcFP hcFN false
  refine ⟨_, hf, ?_, ?_, ?_⟩
  · intro x hx
    simp only [BinaryCostAdapter.binaryCostRule, sub_zero]
    rw [ite_eq_left hx]
  · intro x hx
    simp only [BinaryCostAdapter.binaryCostRule, sub_zero]
    rw [ite_eq_right (not_lt.mpr hx.le), ite_eq_right (ne_of_lt hx)]
  · rw [BinaryCostAdapter.binaryShiftedLoss_eq_table,
      BinaryCostAdapter.binaryPrior_eq_ofReal_smul] at hbayes
    simpa [sub_zero] using hbayes

theorem weightedScore_binary_optimal
    {𝒳 : Type*} [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] [Fintype 𝒳]
    (P0 P1 : 𝒳 → ℝ) (π cFP cFN : ℝ)
    (hP0 : ∀ x, 0 ≤ P0 x) (hP0sum : ∑ x, P0 x = 1)
    (hP1 : ∀ x, 0 ≤ P1 x) (hP1sum : ∑ x, P1 x = 1)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hcFP : 0 < cFP) (hcFN : 0 < cFN) :
    -- (i) A measurable deterministic weighted-score rule exists and is a
    -- Bayes estimator; this is the instantiation of the existing
    -- expected-loss argmin optimality (`IsArgminEstimator.isBayesEstimator`).
    (∃ f : 𝒳 → Bool, ∃ hf : Measurable f,
      (∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x → f x = true)
      ∧ (∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x → f x = false)
      ∧ IsBayesEstimator
          -- the binary 0/1 loss with false-positive cost `cFP` and false-negative cost `cFN`, the finite two-law experiment kernel, and the two-point prior:
          (fun θ y => if θ = y then 0
            else if θ = false then ENNReal.ofReal cFP else ENNReal.ofReal cFN)
          (Kernel.boolKernel
            (∑ x, ENNReal.ofReal (P0 x) • Measure.dirac x)
            (∑ x, ENNReal.ofReal (P1 x) • Measure.dirac x))
          (Kernel.deterministic f hf)
          (ENNReal.ofReal (1 - π) • Measure.dirac false
            + ENNReal.ofReal π • Measure.dirac true))
    -- (ii) Optimality among all randomized rules: any rule following the
    -- strict weighted-score comparisons minimizes the real risk over every
    -- randomized competitor δ.
    ∧ (∀ δ δ' : 𝒳 → ℝ, (∀ x, δ x ∈ Set.Icc (0 : ℝ) 1) → (∀ x, δ' x ∈ Set.Icc (0 : ℝ) 1)
        → (∀ x, (1 - π) * cFP * P0 x < π * cFN * P1 x → δ' x = 1)
        → (∀ x, π * cFN * P1 x < (1 - π) * cFP * P0 x → δ' x = 0)
        → (1 - π) * cFP * (∑ x, P0 x * δ' x) + π * cFN * (∑ x, P1 x * (1 - δ' x))
          ≤ (1 - π) * cFP * (∑ x, P0 x * δ x) + π * cFN * (∑ x, P1 x * (1 - δ x)))
    -- (iii) Genuine tie: at a weighted tie the per-observation contribution
    -- is the same for every randomization level, so arbitrary randomization
    -- there does not change the risk.
    ∧ (∀ x : 𝒳, π * cFN * P1 x = (1 - π) * cFP * P0 x
        → ∀ a b : ℝ, weightedScoreContribution P0 P1 π cFP cFN a x = weightedScoreContribution P0 P1 π cFP cFN b x)
    -- (iv) One-sided support: P0 x = 0 < P1 x strictly favors `true`
    -- (stated as a score inequality; no ratio is formed).
    ∧ (∀ x : 𝒳, P0 x = 0 → 0 < P1 x
        → (1 - π) * cFP * P0 x < π * cFN * P1 x)
    -- (v) Joint-zero support: both weighted scores are 0, the contribution
    -- is 0 for every randomization level, and the point is a genuine tie.
    ∧ (∀ x : 𝒳, P0 x = 0 → P1 x = 0
        → π * cFN * P1 x = (1 - π) * cFP * P0 x
          ∧ ∀ a : ℝ, weightedScoreContribution P0 P1 π cFP cFN a x = 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact weightedScore_bayesRule_exists_aux P0 P1 π cFP cFN hP0 hP0sum hP1 hP1sum hπ0 hπ1 hcFP hcFN
  · intro δ δ' hδ hδ' h1 h0
    have hEq : ∀ η : 𝒳 → ℝ, (1 - π) * cFP * (∑ x, P0 x * η x) + π * cFN * (∑ x, P1 x * (1 - η x))
        = ∑ x, weightedScoreContribution P0 P1 π cFP cFN (η x) x := by
      intro η
      unfold weightedScoreContribution
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hEq δ', hEq δ]
    apply Finset.sum_le_sum
    intro x _
    have hxδ : 0 ≤ δ x ∧ δ x ≤ 1 := Set.mem_Icc.mp (hδ x)
    have hxδ' : 0 ≤ δ' x ∧ δ' x ≤ 1 := Set.mem_Icc.mp (hδ' x)
    rcases lt_trichotomy ((1 - π) * cFP * P0 x) (π * cFN * P1 x) with hlt | heq | hgt
    · have hd : δ' x = 1 := h1 x hlt
      unfold weightedScoreContribution
      rw [hd]
      have h1δ : 0 ≤ 1 - δ x := by linarith [hxδ.2]
      have hS : 0 < π * cFN * P1 x - (1 - π) * cFP * P0 x := by linarith
      have hnn : 0 ≤ (1 - δ x) * (π * cFN * P1 x - (1 - π) * cFP * P0 x) :=
        mul_nonneg h1δ (le_of_lt hS)
      linarith [hnn]
    · unfold weightedScoreContribution
      rw [heq]
      have e1 : δ' x * (π * cFN * P1 x) + (1 - δ' x) * (π * cFN * P1 x) = π * cFN * P1 x := by ring
      have e2 : δ x * (π * cFN * P1 x) + (1 - δ x) * (π * cFN * P1 x) = π * cFN * P1 x := by ring
      rw [e1, e2]
    · have hd : δ' x = 0 := h0 x hgt
      unfold weightedScoreContribution
      rw [hd]
      have hS : 0 < (1 - π) * cFP * P0 x - π * cFN * P1 x := by linarith
      have hnn : 0 ≤ δ x * ((1 - π) * cFP * P0 x - π * cFN * P1 x) :=
        mul_nonneg hxδ.1 (le_of_lt hS)
      linarith [hnn]
  · intro x hx a b
    unfold weightedScoreContribution
    rw [hx]
    ring
  · intro x hx0 hx1
    rw [hx0, mul_zero]
    have h2 : 0 < π * cFN * P1 x := by positivity
    exact h2
  · intro x hx0 hx1
    constructor
    · rw [hx0, hx1, mul_zero, mul_zero]
    · intro a
      unfold weightedScoreContribution
      rw [hx0, hx1, mul_zero, mul_zero, mul_zero, mul_zero, add_zero]


theorem weightedScoreContribution_constant_iff {𝒳 : Type*} (P0 P1 : 𝒳 → ℝ)
    (π cFP cFN : ℝ) (x : 𝒳) :
    (∀ a b : ℝ, weightedScoreContribution P0 P1 π cFP cFN a x
      = weightedScoreContribution P0 P1 π cFP cFN b x)
      ↔ π * cFN * P1 x = (1 - π) * cFP * P0 x := by
  constructor
  · intro h
    have h10 := h 1 0
    simp only [weightedScoreContribution] at h10
    linarith
  · intro h a b
    simp only [weightedScoreContribution, h]
    ring

theorem weightedScore_oneSidedSupport' {𝒳 : Type*} (P0 P1 : 𝒳 → ℝ) (π cFP cFN : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1) (hcFP : 0 < cFP) (hcFN : 0 < cFN) (x : 𝒳)
    (h0 : P1 x = 0) (h1 : 0 < P0 x) :
    π * cFN * P1 x < (1 - π) * cFP * P0 x := by
  rw [h0, mul_zero]
  have h1π : 0 < 1 - π := by linarith
  have hpos : 0 < (1 - π) * cFP * P0 x := by positivity
  exact hpos
end MathlibExt.Probability.Decision
