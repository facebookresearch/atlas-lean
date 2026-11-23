/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.AlphaSpending

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.AlphaSpending

/-- Two equally spaced looks: information times `0, 1/2, 1, 1, …`. -/
noncomputable def τ₂ (k : ℕ) : ℝ := min ((k : ℝ) / 2) 1

theorem τ₂_zero : τ₂ 0 = 0 := by simp [τ₂]

theorem τ₂_mono : Monotone τ₂ := fun _ _ h =>
  min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num))

theorem τ₂_two : τ₂ 2 = 1 := by norm_num [τ₂]

/-- The linear spending function `α t` (power family, exponent one). -/
theorem isAlphaSpendingFunction_linear {α : ℝ} (hα : 0 ≤ α) :
    IsAlphaSpendingFunction α (fun t => α * t) where
  map_zero := by simp
  monotoneOn := fun _ _ _ _ h => mul_le_mul_of_nonneg_left h hα
  map_one_le := by simp

/-! ### Spending function and nominal levels -/

/-- The Pocock-type function at level `0.05` spends `0.05` by the end of the trial. -/
example : pocockSpending (1 / 20) 1 = 1 / 20 := pocockSpending_one _

example : IsAlphaSpendingFunction (1 / 20) (pocockSpending (1 / 20)) :=
  isAlphaSpendingFunction_pocockSpending (by norm_num)

/-- With two looks, the Pocock-type nominal levels sum to exactly `α = 0.05`. -/
example : ∑ k ∈ Finset.range 2, bonferroniLookLevel (pocockSpending (1 / 20)) τ₂ k = 1 / 20 := by
  rw [sum_bonferroniLookLevel, τ₂_two, τ₂_zero]
  simp

/-- Linear spending over two looks gives nominal levels `α/2` and `α/2`. -/
example : bonferroniLookLevel (fun t => 1 / 20 * t) τ₂ 0 = 1 / 40 ∧
    bonferroniLookLevel (fun t => 1 / 20 * t) τ₂ 1 = 1 / 40 := by
  constructor <;> norm_num [bonferroniLookLevel, τ₂]

/-- A concrete trial: p-values `0.001` then `0.5` under linear spending at `α = 0.05`. The
first look (nominal level `0.025`) rejects; the second does not. -/
example : rejectedLooks 2 (bonferroniLookLevel (fun t => 1 / 20 * t) τ₂)
    (fun k => if k = 0 then 1 / 1000 else 1 / 2) = {0} := by
  ext k
  simp only [rejectedLooks, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, h⟩
    interval_cases k
    · rfl
    · norm_num [bonferroniLookLevel, τ₂] at h
  · rintro rfl
    norm_num [bonferroniLookLevel, τ₂]

/-! ### Zero rejections -/

/-- All p-values equal to one: the Bonferroni allocation with a Pocock-type budget at
`α = 0.05` rejects nothing. -/
example : rejectedLooks 2 (bonferroniLookLevel (pocockSpending (1 / 20)) τ₂) (fun _ => 1) = ∅ :=
  rejectedLooks_bonferroniLookLevel_eq_empty_of_eq_one (isAlphaSpendingFunction_pocockSpending
    (by norm_num)) (by norm_num) τ₂_zero τ₂_mono (τ₂_two.le)

/-- No looks, no rejections. -/
example (c p : ℕ → ℝ) : rejectedLooks 0 c p = ∅ := rejectedLooks_zero c p

/-- Boundary: the hypothesis `α < 1` is needed. At `α = 1` with a single look spending
everything, the p-value `1` is rejected. -/
example : rejectedLooks 1 (bonferroniLookLevel (fun t => t) fun k => min (k : ℝ) 1) (fun _ => 1) = {0} := by
  ext k
  simp only [rejectedLooks, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hk, -⟩
    omega
  · rintro rfl
    norm_num [bonferroniLookLevel]

/-! ### Type-I error control: arbitrary dependence across looks -/

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity under perfect dependence: every look reuses the same uniform p-value. The
Bonferroni allocation with a Pocock-type budget and two looks still has type-I error at
most `0.05`. -/
example :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | (rejectedLooks 2 (bonferroniLookLevel (pocockSpending (1 / 20)) τ₂) fun _ => ω).Nonempty} ≤
      ENNReal.ofReal (1 / 20) :=
  measure_rejectedLooks_bonferroniLookLevel_nonempty_le _ (fun _ => id)
    (isAlphaSpendingFunction_pocockSpending (by norm_num)) (by norm_num) τ₂_zero τ₂_mono
    τ₂_two.le fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-- Optional stopping with a data-dependent look: stop at look `1` when the observation is
below `1/2`, otherwise at look `2`. The stopped error is still at most `0.05`. -/
example :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | (if ω < 1 / 2 then 0 else 1) < 2 ∧
        ω ≤ bonferroniLookLevel (pocockSpending (1 / 20)) τ₂ (if ω < 1 / 2 then 0 else 1)} ≤
      ENNReal.ofReal (1 / 20) :=
  measure_reject_at_stopped_look_bonferroni_le _ (fun _ => id) (fun ω => if ω < 1 / 2 then 0 else 1)
    (isAlphaSpendingFunction_pocockSpending (by norm_num)) (by norm_num) τ₂_zero τ₂_mono
    τ₂_two.le fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-- Two endpoints sharing each look's spend equally, all p-values the same uniform variable. -/
example :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | ∃ k < 2, ∃ j ∈ (Finset.univ : Finset (Fin 2)),
        ω ≤ (fun _ : Fin 2 => (1 / 2 : ℝ)) j * bonferroniLookLevel (pocockSpending (1 / 20)) τ₂ k} ≤
      ENNReal.ofReal (1 / 20) :=
  measure_exists_look_endpoint_bonferroni_le _ Finset.univ (fun _ _ => id) (fun _ => 1 / 2)
    (fun _ _ => by norm_num) (by simp) (isAlphaSpendingFunction_pocockSpending (by norm_num))
    (by norm_num) τ₂_zero τ₂_mono τ₂_two.le
    fun _ _ _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-! ### Conservatism of the Bonferroni allocation -/

/-- Two looks with increments `1 / 4, 1 / 4` and independent uniform p-values would reject
with probability `7 / 16`, strictly below the Bonferroni bound `1 / 2`: the allocation is
conservative, not exact Lan–DeMets. -/
example : 1 - (1 - 1 / 4 : ℝ) * (1 - 1 / 4) = 7 / 16 ∧
    (1 - (1 - 1 / 4 : ℝ) * (1 - 1 / 4)) < 1 / 2 := by
  obtain ⟨h1, h2⟩ := two_look_independent_gap (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  refine ⟨by norm_num [h1], by norm_num [h1]⟩

/-! ### Fixed-family testing inflates the error -/

/-- Per-look testing at `α = 0.05` with two looks is only bounded by `2 α = 0.1`. -/
example :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | (rejectedLooks 2 (fun _ => 1 / 20) fun _ => ω).Nonempty} ≤
      ENNReal.ofReal (2 * (1 / 20)) := by
  exact_mod_cast measure_rejectedLooks_const_nonempty_le _ (fun _ => id) (K := 2)
    (by norm_num) (by norm_num) fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id

/-- The inflation is real: some trial with two valid looks tested at `1/4` each has sequential
type-I error strictly above `1/4`. -/
example : ∃ (μ : Measure (Fin 4)) (p : ℕ → Fin 4 → ℝ), IsProbabilityMeasure μ ∧
    (∀ k < 2, IsValidPValue μ (p k)) ∧
    ENNReal.ofReal (1 / 4) <
      μ {ω | (rejectedLooks 2 (fun _ => 1 / 4) fun k => p k ω).Nonempty} := by
  obtain ⟨μ, p, hμ, hp, heq, hlt⟩ := exists_rejectedLooks_const_typeI_eq
  exact ⟨μ, p, hμ, hp, heq ▸ hlt⟩

end MathlibExtTest.Probability.Statistics.MultipleTesting.AlphaSpending
