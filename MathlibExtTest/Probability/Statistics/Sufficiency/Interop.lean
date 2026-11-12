/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Interop
public import MathlibExtTest.Probability.Statistics.Sufficiency.Discrete

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.Sufficiency
open MathlibExtTest.Probability.Statistics.Sufficiency.Discrete
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Statistics.Sufficiency.Interop

/-- The identity statistic is sufficient for every finite family, through the bridge. -/
example {Θ X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (P : Θ → PMF X) :
    IsSufficient (MeasurableSpace.comap (id : X → X) ‹MeasurableSpace X›)
      fun θ => (P θ).toMeasure := by
  refine IsSufficientPMF.isSufficient_comap (T := id) ?_
  intro θ θ' x h h'
  simp only [PMF.map_id, id_eq] at h h' ⊢
  rw [ENNReal.div_self h (PMF.apply_ne_top _ _), ENNReal.div_self h' (PMF.apply_ne_top _ _)]

/-- Negative check: a constant statistic discards the observation and is not sufficient for
the two point masses on `Bool`. -/
example : ¬ IsSufficientPMF (fun b : Bool => PMF.pure b) (fun _ : Bool => ()) := by
  intro hT
  have h1 : (PMF.pure true).map (fun _ : Bool => ()) () ≠ 0 := by simp [PMF.pure_map]
  have h2 : (PMF.pure false).map (fun _ : Bool => ()) () ≠ 0 := by simp [PMF.pure_map]
  have h := hT true false true h1 h2
  simp [PMF.pure_map, PMF.pure_apply] at h

/-- `n = 0`: on a one-point observation space every statistic is sufficient. -/
example {Θ : Type*} (P : Θ → PMF Unit) : IsSufficientPMF P (fun _ : Unit => ()) := by
  change IsSufficientPMF P id
  intro θ θ' x h h'
  simp only [PMF.map_id, id_eq] at h h' ⊢
  rw [ENNReal.div_self h (PMF.apply_ne_top _ _), ENNReal.div_self h' (PMF.apply_ne_top _ _)]

/-- Worked Bernoulli-count validation: the success count is sufficient for two Bernoulli
tosses, and for the first-toss estimator the Rao–Blackwell split from the named theorem
has strictly positive residual at `θ = 1 / 2`. The positivity is independent of the
witness `φ`: on the fiber `{heads = 1}` (mass `1 / 2`) the estimator is `0`/`1` with
conditional mass `1 / 2` each, so `(W - φ 1)²` integrates to at least `1 / 8`. -/
example :
    ∃ φ : ℕ → ℝ, Measurable φ ∧
      (∀ θ : {θ : ℝ≥0 // θ ≤ 1},
        ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) - (1 / 2 : ℝ)) ^ 2 ∂(twoCoins θ).toMeasure =
        ∫ ω, (φ (heads ω) - 1 / 2) ^ 2 ∂(twoCoins θ).toMeasure +
        ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) - φ (heads ω)) ^ 2 ∂(twoCoins θ).toMeasure) ∧
      0 < ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) -
        φ (heads ω)) ^ 2 ∂(twoCoins (⟨1 / 2, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure := by
  have hW : ∀ θ : {θ : ℝ≥0 // θ ≤ 1},
      MemLp (fun x : Bool × Bool => if x.1 then (1 : ℝ) else 0) 2 (twoCoins θ).toMeasure := by
    intro θ
    refine MemLp.of_bound Measurable.of_discrete.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rcases x with ⟨b₁, b₂⟩
    cases b₁ <;> simp
  obtain ⟨φ, hφ, hpyth⟩ :=
    IsSufficientPMF.raoBlackwell_comap_sq heads_sufficient hW (fun _ => 1 / 2)
  refine ⟨φ, hφ, hpyth, ?_⟩
  have hmass : ∀ x : Bool × Bool,
      (twoCoins (⟨1 / 2, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure.real {x} = 1 / 4 := by
    intro x
    rcases x with ⟨_ | _, _ | _⟩ <;>
      simp [Measure.real_def, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        twoCoins, coin] <;>
      norm_num
  have hφT : Measurable (fun ω : Bool × Bool => φ (heads ω)) :=
    hφ.comp Measurable.of_discrete
  have hint : Integrable
      (fun ω : Bool × Bool => ((if ω.1 then (1 : ℝ) else 0) - φ (heads ω)) ^ 2)
      (twoCoins (⟨1 / 2, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure := by
    refine Integrable.of_bound
      ((Measurable.of_discrete.sub hφT).pow_const 2).aestronglyMeasurable
      (∑ x : Bool × Bool, ‖((if x.1 then (1 : ℝ) else 0) - φ (heads x)) ^ 2‖) ?_
    exact ae_of_all _ fun ω =>
      Finset.single_le_sum
        (f := fun x : Bool × Bool => ‖((if x.1 then (1 : ℝ) else 0) - φ (heads x)) ^ 2‖)
        (fun x _ => norm_nonneg _) (Finset.mem_univ ω)
  have e1 : heads (true, true) = 2 := rfl
  have e2 : heads (true, false) = 1 := rfl
  have e3 : heads (false, true) = 1 := rfl
  have e4 : heads (false, false) = 0 := rfl
  rw [integral_fintype hint]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hmass, e1, e2, e3, e4, smul_eq_mul]
  simp
  nlinarith [sq_nonneg (φ 1 - 1 / 2), sq_nonneg (φ 2 - 1), sq_nonneg (φ 0)]

/-- Degenerate case: at `θ = 0` the count is constantly `0`, the estimator vanishes
almost surely, and the split forces the residual to `0`. -/
example :
    ∃ φ : ℕ → ℝ, Measurable φ ∧
      (∀ θ : {θ : ℝ≥0 // θ ≤ 1},
        ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) - (0 : ℝ)) ^ 2 ∂(twoCoins θ).toMeasure =
        ∫ ω, (φ (heads ω) - 0) ^ 2 ∂(twoCoins θ).toMeasure +
        ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) - φ (heads ω)) ^ 2 ∂(twoCoins θ).toMeasure) ∧
      ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) -
        φ (heads ω)) ^ 2 ∂(twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure = 0 := by
  have hW : ∀ θ : {θ : ℝ≥0 // θ ≤ 1},
      MemLp (fun x : Bool × Bool => if x.1 then (1 : ℝ) else 0) 2 (twoCoins θ).toMeasure := by
    intro θ
    refine MemLp.of_bound Measurable.of_discrete.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rcases x with ⟨b₁, b₂⟩
    cases b₁ <;> simp
  obtain ⟨φ, hφ, hpyth⟩ :=
    IsSufficientPMF.raoBlackwell_comap_sq heads_sufficient hW (fun _ => 0)
  refine ⟨φ, hφ, hpyth, ?_⟩
  have htot : ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) - 0) ^ 2
      ∂(twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure = 0 := by
    have m1 : (twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure.real
        {(true, true)} = 0 := by
      simp [Measure.real_def, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        twoCoins, coin]
    have m2 : (twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure.real
        {(true, false)} = 0 := by
      simp [Measure.real_def, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        twoCoins, coin]
    have m3 : (twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure.real
        {(false, true)} = 0 := by
      simp [Measure.real_def, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        twoCoins, coin]
    have m4 : (twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure.real
        {(false, false)} = 1 := by
      simp [Measure.real_def, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
        twoCoins, coin]
    have hint : Integrable
        (fun ω : Bool × Bool => ((if ω.1 then (1 : ℝ) else 0) - 0) ^ 2)
        (twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure := by
      refine Integrable.of_bound
        ((Measurable.of_discrete.sub measurable_const).pow_const 2).aestronglyMeasurable
        (∑ x : Bool × Bool, ‖((if x.1 then (1 : ℝ) else 0) - 0) ^ 2‖) ?_
      exact ae_of_all _ fun ω =>
        Finset.single_le_sum
          (f := fun x : Bool × Bool => ‖((if x.1 then (1 : ℝ) else 0) - 0) ^ 2‖)
          (fun x _ => norm_nonneg _) (Finset.mem_univ ω)
    rw [integral_fintype hint]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, m1, m2, m3, m4, smul_eq_mul]
    simp
  have hsplit := hpyth (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})
  rw [htot] at hsplit
  have hn1 : 0 ≤ ∫ ω, (φ (heads ω) - 0) ^ 2
      ∂(twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure :=
    integral_nonneg fun ω => sq_nonneg _
  have hn2 : 0 ≤ ∫ (ω : Bool × Bool), ((if ω.1 then (1 : ℝ) else 0) - φ (heads ω)) ^ 2
      ∂(twoCoins (⟨0, by norm_num⟩ : {θ : ℝ≥0 // θ ≤ 1})).toMeasure :=
    integral_nonneg fun ω => sq_nonneg _
  linarith

end MathlibExtTest.Probability.Statistics.Sufficiency.Interop
