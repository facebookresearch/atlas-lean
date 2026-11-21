/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Factorial
public import MathlibExt.Probability.Statistics.SaturatedTwoByTwoRegression

import Mathlib.Tactic

@[expose] public section

open Matrix


/-!
# Tests for the saturated two-by-two regression

* An unbalanced seven-observation sample with cell means `2, 5, 3, 11`: OLS coefficients
  `(2, 1, 3, 5)`, interaction `5`, fitted values the cell means; the contrast of cell totals is
  `15`, not `5`.
* An empty cell: the Gram matrix is singular, two least-squares solutions disagree on the
  interaction, and OLS returns the zero vector while the contrast with the junk mean is `-5`.
* One observation per cell: a pre-period regression with interaction `0` next to a
  post-period regression with interaction `3` whose treatment effect is `1` (future
  confounding); interaction `1` in levels and `0` in logs.
* The regression interaction is twice the factorial interaction effect `interactionAB`. -/

namespace MathlibExtTest.Probability.Statistics.SaturatedTwoByTwoRegression

open Finset ProbabilityTheory MathlibExt.Probability.Statistics.LinearModel
  MathlibExt.Probability.Statistics.Experiment
  MathlibExt.Probability.Statistics.SaturatedTwoByTwoRegression

/-- Evaluation aid for the fixtures: a group mean as a ratio of two sums over all
observations. -/
private theorem groupMean_eq_sum_ite {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (x : ι → ℝ) (g : G) :
    groupMean grp x g =
      (∑ i, if grp i = g then x i else 0) / ∑ i, if grp i = g then (1 : ℝ) else 0 := by
  rw [groupMean, Finset.sum_filter, Finset.natCast_card_filter]

/-! ### Convention: factorial interaction effect -/

/-- The regression interaction is twice Atlas's factorial interaction effect `interactionAB`
(Dasgupta–Pillai–Rubin normalization) of the same four cell means. -/
theorem interaction_eq_two_mul_interactionAB {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d t : ι → Bool} (hcell : ∀ a b, ∃ i, d i = a ∧ t i = b) (y : ι → ℝ) :
    olsEstimator (twoByTwoDesign d t) y 3 =
      2 * interactionAB (groupMean (fun i => (d i, t i)) y (false, false))
        (groupMean (fun i => (d i, t i)) y (false, true))
        (groupMean (fun i => (d i, t i)) y (true, false))
        (groupMean (fun i => (d i, t i)) y (true, true)) := by
  rw [olsEstimator_twoByTwoDesign_interaction hcell, interactionAB]
  ring

/-! ### An unbalanced sample with four populated cells -/

/-- Group of seven observations: three control (`false`), four treated (`true`). -/
def unbalancedGroup : Fin 7 → Bool := ![false, false, false, true, true, true, true]

/-- Period: control observed twice before and once after, treated twice before and twice
after. -/
def unbalancedPeriod : Fin 7 → Bool := ![false, false, true, false, false, true, true]

/-- Outcomes; the cell means are `m₀₀ = 2`, `m₀₁ = 5`, `m₁₀ = 3`, `m₁₁ = 11`. -/
noncomputable def unbalancedOutcome : Fin 7 → ℝ := ![1, 3, 5, 2, 4, 10, 12]

theorem unbalanced_cells : ∀ a b, ∃ i, unbalancedGroup i = a ∧ unbalancedPeriod i = b := by
  decide

theorem unbalanced_cellMeans :
    groupMean (fun i => (unbalancedGroup i, unbalancedPeriod i)) unbalancedOutcome
        (false, false) = 2 ∧
      groupMean (fun i => (unbalancedGroup i, unbalancedPeriod i)) unbalancedOutcome
        (false, true) = 5 ∧
      groupMean (fun i => (unbalancedGroup i, unbalancedPeriod i)) unbalancedOutcome
        (true, false) = 3 ∧
      groupMean (fun i => (unbalancedGroup i, unbalancedPeriod i)) unbalancedOutcome
        (true, true) = 11 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [groupMean_eq_sum_ite] <;>
    simp [-Finset.sum_boole, Fin.sum_univ_succ, unbalancedGroup, unbalancedPeriod,
      unbalancedOutcome] <;>
    norm_num

/-- The populated cells give a full-rank design. -/
theorem unbalanced_isUnit_gram :
    IsUnit ((twoByTwoDesign unbalancedGroup unbalancedPeriod)ᵀ *
      twoByTwoDesign unbalancedGroup unbalancedPeriod) :=
  (isUnit_gram_twoByTwoDesign_iff _ _).mpr unbalanced_cells

/-- OLS coefficients `(m₀₀, m₁₀ - m₀₀, m₀₁ - m₀₀, (m₁₁ - m₁₀) - (m₀₁ - m₀₀)) = (2, 1, 3, 5)`. -/
theorem unbalanced_olsEstimator :
    olsEstimator (twoByTwoDesign unbalancedGroup unbalancedPeriod) unbalancedOutcome =
      ![2, 1, 3, 5] := by
  obtain ⟨h00, h01, h10, h11⟩ := unbalanced_cellMeans
  rw [olsEstimator_twoByTwoDesign unbalanced_cells, cellMeanCoefficients, h00, h01, h10, h11]
  norm_num

/-- The interaction coefficient is the four-cell contrast `(11 - 3) - (5 - 2) = 5`. -/
theorem unbalanced_interaction :
    olsEstimator (twoByTwoDesign unbalancedGroup unbalancedPeriod) unbalancedOutcome 3 = 5 := by
  obtain ⟨h00, h01, h10, h11⟩ := unbalanced_cellMeans
  rw [olsEstimator_twoByTwoDesign_interaction unbalanced_cells, h00, h01, h10, h11]
  norm_num

/-- Every solution of the normal equations has interaction `5`, not only `olsEstimator`. -/
theorem unbalanced_normal_eq_interaction (β : Fin 4 → ℝ)
    (hβ : ((twoByTwoDesign unbalancedGroup unbalancedPeriod)ᵀ *
        twoByTwoDesign unbalancedGroup unbalancedPeriod) *ᵥ β =
      (twoByTwoDesign unbalancedGroup unbalancedPeriod)ᵀ *ᵥ unbalancedOutcome) :
    β 3 = 5 := by
  obtain ⟨h00, h01, h10, h11⟩ := unbalanced_cellMeans
  rw [(twoByTwoDesign_normal_eq_iff unbalanced_cells unbalancedOutcome β).mp hβ,
    cellMeanCoefficients, h00, h01, h10, h11]
  norm_num

/-- The design at the coefficients `(2, 1, 3, 5)` returns the cell mean of every observation. -/
theorem unbalanced_design_mulVec :
    twoByTwoDesign unbalancedGroup unbalancedPeriod *ᵥ ![2, 1, 3, 5] =
      ![2, 2, 5, 3, 3, 11, 11] := by
  rw [twoByTwoDesign_mulVec]
  funext i
  fin_cases i <;> simp [unbalancedGroup, unbalancedPeriod] <;> norm_num

/-- The OLS fitted values are the cell means: the fit depends on an observation only through
its cell. -/
theorem unbalanced_fitted :
    twoByTwoDesign unbalancedGroup unbalancedPeriod *ᵥ
        olsEstimator (twoByTwoDesign unbalancedGroup unbalancedPeriod) unbalancedOutcome =
      ![2, 2, 5, 3, 3, 11, 11] := by
  obtain ⟨h00, h01, h10, h11⟩ := unbalanced_cellMeans
  rw [olsEstimator_twoByTwoDesign unbalanced_cells, twoByTwoDesign_mulVec_cellMeanCoefficients]
  funext i
  fin_cases i
  exacts [h00, h00, h01, h10, h10, h11, h11]

/-- Omitted denominators: in an unbalanced sample the same contrast of cell totals,
`(22 - 6) - (5 - 4) = 15`, is not the interaction coefficient `5`. -/
theorem unbalanced_interaction_ne_total_contrast :
    olsEstimator (twoByTwoDesign unbalancedGroup unbalancedPeriod) unbalancedOutcome 3 ≠
      ((∑ i with (unbalancedGroup i, unbalancedPeriod i) = (true, true), unbalancedOutcome i) -
          ∑ i with (unbalancedGroup i, unbalancedPeriod i) = (true, false), unbalancedOutcome i) -
        ((∑ i with (unbalancedGroup i, unbalancedPeriod i) = (false, true), unbalancedOutcome i) -
          ∑ i with (unbalancedGroup i, unbalancedPeriod i) = (false, false),
            unbalancedOutcome i) := by
  rw [unbalanced_interaction]
  simp [Finset.sum_filter, Fin.sum_univ_succ, unbalancedGroup, unbalancedPeriod,
    unbalancedOutcome]
  norm_num

/-! ### An empty cell: rank, zero mass and identification -/

/-- Three observations and no treated observation after: the cell `(true, true)` is empty. -/
def emptyGroup : Fin 3 → Bool := ![false, false, true]

def emptyPeriod : Fin 3 → Bool := ![false, true, false]

noncomputable def emptyOutcome : Fin 3 → ℝ := ![1, 2, 4]

/-- With an empty cell the Gram matrix is singular. -/
theorem empty_cell_not_isUnit_gram :
    ¬ IsUnit ((twoByTwoDesign emptyGroup emptyPeriod)ᵀ *
      twoByTwoDesign emptyGroup emptyPeriod) := by
  rw [isUnit_gram_twoByTwoDesign_iff]
  intro h
  obtain ⟨i, hi⟩ := h true true
  fin_cases i <;> simp [emptyGroup, emptyPeriod] at hi

/-- With an empty cell the interaction is not identified: two solutions of the normal
equations have interactions differing by `1`. -/
theorem empty_cell_interaction_not_identified :
    ∃ β β' : Fin 4 → ℝ,
      ((twoByTwoDesign emptyGroup emptyPeriod)ᵀ * twoByTwoDesign emptyGroup emptyPeriod) *ᵥ β =
          (twoByTwoDesign emptyGroup emptyPeriod)ᵀ *ᵥ emptyOutcome ∧
        ((twoByTwoDesign emptyGroup emptyPeriod)ᵀ * twoByTwoDesign emptyGroup emptyPeriod) *ᵥ β' =
          (twoByTwoDesign emptyGroup emptyPeriod)ᵀ *ᵥ emptyOutcome ∧
        β 3 ≠ β' 3 := by
  have hnull : twoByTwoDesign emptyGroup emptyPeriod *ᵥ Pi.single 3 1 = 0 := by
    rw [twoByTwoDesign_mulVec]
    funext i
    fin_cases i <;> simp [emptyGroup, emptyPeriod]
  refine ⟨cellMeanCoefficients emptyGroup emptyPeriod emptyOutcome,
    cellMeanCoefficients emptyGroup emptyPeriod emptyOutcome + Pi.single 3 1,
    gram_mulVec_cellMeanCoefficients _ _ _, ?_, ?_⟩
  · rw [Matrix.mulVec_add, gram_mulVec_cellMeanCoefficients, ← Matrix.mulVec_mulVec, hnull,
      Matrix.mulVec_zero, add_zero]
  · simp

/-- The populated-cell hypothesis of `olsEstimator_twoByTwoDesign_interaction` cannot be
dropped: here OLS returns its junk zero vector (Mathlib's inverse of a singular matrix is `0`),
while the contrast built from the empty cell's junk mean `0` is `(0 - 4) - (2 - 1) = -5`. -/
theorem empty_cell_olsEstimator_ne_contrast :
    olsEstimator (twoByTwoDesign emptyGroup emptyPeriod) emptyOutcome 3 = 0 ∧
      (groupMean (fun i => (emptyGroup i, emptyPeriod i)) emptyOutcome (true, true) -
          groupMean (fun i => (emptyGroup i, emptyPeriod i)) emptyOutcome (true, false)) -
        (groupMean (fun i => (emptyGroup i, emptyPeriod i)) emptyOutcome (false, true) -
          groupMean (fun i => (emptyGroup i, emptyPeriod i)) emptyOutcome (false, false)) =
        -5 := by
  have hdet : ¬ IsUnit ((twoByTwoDesign emptyGroup emptyPeriod)ᵀ *
      twoByTwoDesign emptyGroup emptyPeriod).det := fun h =>
    empty_cell_not_isUnit_gram ((Matrix.isUnit_iff_isUnit_det _).mpr h)
  refine ⟨?_, ?_⟩
  · simp [olsEstimator, olsMatrix,
      MathlibExt.Probability.Statistics.GeneralizedLeastSquares.glsMatrix,
      Matrix.nonsing_inv_apply_not_isUnit _ hdet]
  · simp only [groupMean_eq_sum_ite]
    simp [-Finset.sum_boole, Fin.sum_univ_succ, emptyGroup, emptyPeriod, emptyOutcome]
    norm_num

/-! ### One observation per cell: pretrends and transformations -/

/-- Control before, control after, treated before, treated after. -/
def cellGroup : Fin 4 → Bool := ![false, false, true, true]

def cellPeriod : Fin 4 → Bool := ![false, true, false, true]

theorem singleton_cells : ∀ a b, ∃ i, cellGroup i = a ∧ cellPeriod i = b := by
  decide

/-- With one observation per cell the interaction is `(y₃ - y₂) - (y₁ - y₀)`. -/
theorem singleton_interaction (y : Fin 4 → ℝ) :
    olsEstimator (twoByTwoDesign cellGroup cellPeriod) y 3 = (y 3 - y 2) - (y 1 - y 0) := by
  rw [olsEstimator_twoByTwoDesign_interaction singleton_cells]
  simp only [groupMean_eq_sum_ite]
  simp [-Finset.sum_boole, Fin.sum_univ_succ, cellGroup, cellPeriod]

/-- Pre-window outcomes (periods `-1` and `0`): both groups rise by `1`. -/
noncomputable def preOutcome : Fin 4 → ℝ := ![1, 2, 1, 2]

/-- Untreated potential outcomes in the main window (periods `0` and `1`): the treated group
would have risen by `3`, the control group rises by `1`. -/
noncomputable def untreatedMain : Fin 4 → ℝ := ![2, 3, 2, 5]

/-- Observed outcomes in the main window: the treated group after treatment gains `1` over its
untreated potential outcome. -/
noncomputable def observedMain : Fin 4 → ℝ := ![2, 3, 2, 6]

/-- **Zero pretrend, future confounding**: the pre-window interaction is `0`, yet the
main-window interaction `3` is the treatment effect `1` plus the interaction `2` of the
untreated potential outcomes. A flat pretrend does not establish parallel trends. -/
theorem zero_pretrend_future_confounding :
    olsEstimator (twoByTwoDesign cellGroup cellPeriod) preOutcome 3 = 0 ∧
      olsEstimator (twoByTwoDesign cellGroup cellPeriod) observedMain 3 = 3 ∧
      olsEstimator (twoByTwoDesign cellGroup cellPeriod) untreatedMain 3 = 2 ∧
      groupMean (fun i => (cellGroup i, cellPeriod i)) (fun i => observedMain i - untreatedMain i)
        (true, true) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [singleton_interaction]
    norm_num [preOutcome]
  · rw [singleton_interaction]
    norm_num [observedMain]
  · rw [singleton_interaction]
    norm_num [untreatedMain]
  · rw [groupMean_eq_sum_ite]
    simp [-Finset.sum_boole, Fin.sum_univ_succ, cellGroup, cellPeriod, observedMain,
      untreatedMain]
    norm_num

/-- Levels `1, 2` (control) and `2, 4` (treated). -/
noncomputable def levelOutcome : Fin 4 → ℝ := ![1, 2, 2, 4]

/-- **Level and log scales disagree**: the interaction is `1` in levels and `0` in logs. -/
theorem level_log_interaction :
    olsEstimator (twoByTwoDesign cellGroup cellPeriod) levelOutcome 3 = 1 ∧
      olsEstimator (twoByTwoDesign cellGroup cellPeriod) (fun i => Real.log (levelOutcome i)) 3 =
        0 := by
  refine ⟨?_, ?_⟩
  · rw [singleton_interaction]
    norm_num [levelOutcome]
  · rw [singleton_interaction]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    simp [levelOutcome, h4]
    ring

end MathlibExtTest.Probability.Statistics.SaturatedTwoByTwoRegression
