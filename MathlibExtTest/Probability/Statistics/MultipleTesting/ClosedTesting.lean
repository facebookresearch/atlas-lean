/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.ClosedTesting

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.ClosedTesting

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- Closure by hand at `α = 0.05`: `H₂` (p-value `0.5`) is kept because the local Bonferroni
test of `H_{{2}}` does not reject, while `H₀` is rejected by every local test containing it. -/
example : 2 ∉ closedRejections (bonferroniLocalTest (1 / 20) p3) := by
  rw [mem_closedRejections]
  intro h
  obtain ⟨j, hj, hle⟩ := h {2} (Finset.mem_singleton_self 2)
  rw [Finset.mem_singleton] at hj
  subst hj
  norm_num [p3] at hle

/-- `H₀` survives every local test: its p-value `0.01` is below `α / |J| ≥ 0.05 / 3`. -/
example : 0 ∈ closedRejections (bonferroniLocalTest (1 / 20) p3) := by
  rw [mem_closedRejections]
  intro J hJ
  refine ⟨0, hJ, ?_⟩
  have hc : (J.card : ℝ) ≤ 3 := by exact_mod_cast (Finset.card_le_univ J).trans_eq (by simp)
  have hpos : (0 : ℝ) < J.card := by exact_mod_cast Finset.card_pos.mpr ⟨0, hJ⟩
  rw [le_div_iff₀ hpos]
  norm_num [p3]
  linarith

/-- Holm's rejections computed through the closure: the two smallest p-values. -/
example : closedRejections (bonferroniLocalTest (1 / 20) p3) = {0, 1} := by
  rw [← holmRejections_eq_closedRejections (by norm_num)]
  have h60 : numBelow p3 ((1 / 20) / ((3 : ℕ) - (1 : ℕ) + 1)) = 1 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ (1 / 20) / ((3 : ℕ) - (1 : ℕ) + 1)) = {0} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have h40 : numBelow p3 ((1 / 20) / ((3 : ℕ) - (2 : ℕ) + 1)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ (1 / 20) / ((3 : ℕ) - (2 : ℕ) + 1)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have h20 : numBelow p3 ((1 / 20) / ((3 : ℕ) - (3 : ℕ) + 1)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ (1 / 20) / ((3 : ℕ) - (3 : ℕ) + 1)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have hidx : holmIndex (1 / 20) p3 = 2 := by
    have hge : 2 ≤ holmIndex (1 / 20) p3 := by
      refine le_holmIndex (by norm_num) fun k hk => ?_
      rcases Finset.mem_Icc.1 hk with ⟨hk₁, hk₂⟩
      interval_cases k
      · rw [h60]
      · rw [h40]
    have hne : holmIndex (1 / 20) p3 ≠ 3 := by
      intro h3
      have := le_numBelow_of_le_holmIndex (α := 1 / 20) (p := p3) (k := 3) (by norm_num) h3.ge
      rw [h20] at this
      omega
    have hle := holmIndex_le (1 / 20) p3
    omega
  rw [holmRejections, hidx]
  ext i
  fin_cases i <;> norm_num [p3]

/-- The empty intersection hypothesis is never rejected by a Bonferroni local test. -/
example (α : ℝ) (p : Fin 3 → ℝ) : ¬ bonferroniLocalTest α p ∅ := by
  simp [bonferroniLocalTest]

/-- Boundary: with local tests that never reject, the closed procedure rejects nothing. -/
example : closedRejections (fun _ : Finset (Fin 3) => False) = ∅ := by
  ext i
  simp only [mem_closedRejections, imp_false, Finset.notMem_empty, iff_false, not_forall,
    not_not]
  exact ⟨{i}, Finset.mem_singleton_self i⟩

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity and no independence: all `m` p-values equal one uniform variable and every null
is true; the closure of the Bonferroni local tests controls the FWER at `α`. -/
example (m : ℕ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | (closedRejections (fun J => bonferroniLocalTest α (fun _ : Fin m => ω) J) ∩
        Finset.univ).Nonempty} ≤ ENNReal.ofReal α :=
  measure_closed_familywiseError_le _ (fun J ω => bonferroniLocalTest α (fun _ => ω) J)
    Finset.univ (measure_bonferroniLocalTest_le _ (fun _ => id) Finset.univ
      (fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id) hα₀ hα₁)

end MathlibExtTest.Probability.Statistics.MultipleTesting.ClosedTesting
