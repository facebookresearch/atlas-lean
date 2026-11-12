/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Assignment

/-!
# Tests for the complete-randomization assignment law

* Boundary assignments: no treated units and all units treated give point masses; more treated
  units than the population gives the zero measure, which is not a probability measure.
* A direct evaluation of the bridge to `randExp` on three units.
* Two units, one per arm: unbiasedness and the variance identity apply, and the arm-size
  hypothesis of the Neyman-estimator results fails.
* Four units, two per arm: equality for a constant effect and strict conservativeness for a
  heterogeneous one.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Experiment

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Causality MathlibExt.Probability.Statistics.Experiment

/-- Empty assignment `n₁ = 0`: the law is the point mass at `∅` (a probability measure). -/
example (ι : Type*) [Fintype ι] : completeRandomization ι 0 = Measure.dirac ∅ := by
  rw [completeRandomization_eq, Measure.uniformOfFinset, powersetCard_zero, sum_singleton,
    card_singleton, Nat.cast_one, inv_one, one_smul]

/-- Full assignment `n₁ = N`: the law is the point mass at `univ`. -/
example (ι : Type*) [Fintype ι] :
    completeRandomization ι (Fintype.card ι) = Measure.dirac univ := by
  rw [completeRandomization_eq, Measure.uniformOfFinset, ← card_univ, powersetCard_self,
    sum_singleton, card_singleton, Nat.cast_one, inv_one, one_smul]

/-- Too many treated units: the law is the zero measure, so it is not a probability measure. -/
example : completeRandomization (Fin 2) 3 = 0 := by
  rw [completeRandomization_eq, Measure.uniformOfFinset,
    powersetCard_eq_empty.2 (by simp), sum_empty]

example : ¬ IsProbabilityMeasure (completeRandomization (Fin 2) 3) := by
  intro h
  have h0 : completeRandomization (Fin 2) 3 = 0 := by
    rw [completeRandomization_eq, Measure.uniformOfFinset,
      powersetCard_eq_empty.2 (by simp), sum_empty]
  rw [h0] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure (Finset (Fin 2))) rfl

/-- Bridge non-vacuity: one treated unit among three, probability `1/3` that unit `0` is
treated. -/
example : ∫ S, (if (0 : Fin 3) ∈ S then (1 : ℝ) else 0) ∂(completeRandomization (Fin 3) 1) =
    1 / 3 := by
  rw [integral_completeRandomization (by simp), randExp, powersetCard_one, sum_map]
  simp

/-- `N = 2`, one unit per arm: unbiasedness and the exact variance identity apply. -/
example (y₀ y₁ : Fin 2 → ℝ) :
    ∫ S, diffInMeans y₀ y₁ S ∂(completeRandomization (Fin 2) 1) = ate y₀ y₁ :=
  integral_diffInMeans_completeRandomization y₀ y₁ le_rfl (by simp)

example (y₀ y₁ : Fin 2 → ℝ) :
    variance (diffInMeans y₀ y₁) (completeRandomization (Fin 2) 1) =
      popVar y₁ / (1 : ℕ) + popVar y₀ / ((Fintype.card (Fin 2) : ℝ) - (1 : ℕ)) -
        popVar (fun i => y₁ i - y₀ i) / Fintype.card (Fin 2) :=
  variance_diffInMeans_completeRandomization y₀ y₁ le_rfl (by simp)

/-- `N = 2`, one unit per arm: the Neyman-estimator corollaries cannot be instantiated, since
their arm-size hypothesis `n₁ + 2 ≤ N` fails at `n₁ = 1`. -/
example : ¬ ((1 : ℕ) + 2 ≤ Fintype.card (Fin 2)) := by
  simp

/-- `N = 4`, two units per arm, constant effect: Neyman's estimator is exact. -/
example (y₀ : Fin 4 → ℝ) (c : ℝ) :
    variance (diffInMeans y₀ (fun i => y₀ i + c)) (completeRandomization (Fin 4) 2) =
      ∫ S, neymanVar y₀ (fun i => y₀ i + c) S ∂(completeRandomization (Fin 4) 2) := by
  exact (variance_diffInMeans_le_integral_neymanVar y₀ (fun i => y₀ i + c) le_rfl
    (by simp)).2.2 ⟨c, fun i => by simp⟩

/-- `N = 4`, two units per arm, heterogeneous effect: Neyman's estimator is strictly
conservative. -/
example :
    variance (diffInMeans (fun _ : Fin 4 => (0 : ℝ)) (fun i => if i = 0 then 1 else 0))
        (completeRandomization (Fin 4) 2) <
      ∫ S, neymanVar (fun _ : Fin 4 => (0 : ℝ)) (fun i => if i = 0 then 1 else 0) S
        ∂(completeRandomization (Fin 4) 2) := by
  have h := variance_diffInMeans_le_integral_neymanVar (fun _ : Fin 4 => (0 : ℝ))
    (fun i => if i = 0 then 1 else 0) le_rfl (by simp)
  refine lt_of_le_of_ne h.1 fun heq => ?_
  obtain ⟨c, hc⟩ := h.2.1 heq
  have h0 := hc 0
  have h1 := hc 1
  simp at h0 h1
  linarith

end MathlibExtTest.Probability.Statistics.Experiment
