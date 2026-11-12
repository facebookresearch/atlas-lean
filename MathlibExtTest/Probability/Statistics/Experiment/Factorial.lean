/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Experiment.Factorial
public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# Tests for 2x2 factorial unbiasedness

Nonadditive and additive population fixtures, the one-unit-per-cell use case,
and the empty-cell-size exclusion.
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

namespace MathlibExtTest.Probability.Statistics.Experiment

open MathlibExt.Probability.Statistics.Experiment
open MathlibExt.Probability.Causality

theorem popMean_const_fin4 (c : ℝ) : popMean (fun _ : Fin 4 => c) = c := by
  unfold popMean
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Nonadditive population fixture: constant surfaces `1, 0, 0, 1` give
population main effects `0` and interaction `1`. -/
example : mainEffectA (popMean (fun _ : Fin 4 => (1 : ℝ)))
    (popMean (fun _ : Fin 4 => (0 : ℝ))) (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) = 0 := by
  simp only [popMean_const_fin4, mainEffectA]
  norm_num

example : interactionAB (popMean (fun _ : Fin 4 => (1 : ℝ)))
    (popMean (fun _ : Fin 4 => (0 : ℝ))) (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) = 1 := by
  simp only [popMean_const_fin4, interactionAB]
  norm_num

/-- Additive population fixture: constant surfaces `0, 1, 2, 3` give
interaction `0` while the main effects recover the additive shifts. -/
example : interactionAB (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) (popMean (fun _ : Fin 4 => (2 : ℝ)))
    (popMean (fun _ : Fin 4 => (3 : ℝ))) = 0 := by
  simp only [popMean_const_fin4, interactionAB]
  norm_num

example : mainEffectA (popMean (fun _ : Fin 4 => (0 : ℝ)))
    (popMean (fun _ : Fin 4 => (1 : ℝ))) (popMean (fun _ : Fin 4 => (2 : ℝ)))
    (popMean (fun _ : Fin 4 => (3 : ℝ))) = 2 := by
  simp only [popMean_const_fin4, mainEffectA]
  norm_num

/-- Use case: one unit per cell, the per-cell unbiasedness instance. -/
example (y : Fin 4 → ℝ) :
    ∫ f, factorialCellMean y 0 f ∂(cellAssignment fun _ => 1) =
      popMean y := by
  exact integral_factorialCellMean y 0 (fun _ => 1) (fun _ => one_pos) (by decide)

/-- Negative: the all-ones-except-cell-zero size function violates the
positivity hypothesis, so unbiasedness is not claimed for it. -/
example : ¬ ∀ c, 0 < (![0, 1, 1, 1] : Fin 4 → ℕ) c := by
  intro h
  have h0 := h 0
  simp at h0

/-- Main-effect A unbiasedness applied to the constant nonadditive fixture
(effect `0`). -/
example : (∫ f, mainEffectA (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 0 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 1 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 2 f)
    (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 3 f)
    ∂(cellAssignment fun _ => 1)) = 0 := by
  rw [integral_mainEffectA _ _ _ _ _ (fun _ => one_pos) (by decide)]
  simp only [popMean_const_fin4, mainEffectA]
  norm_num

/-- Main-effect B unbiasedness applied to the constant additive fixture
(effect `1`). -/
example : (∫ f, mainEffectB (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 0 f)
    (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 1 f)
    (factorialCellMean (fun _ : Fin 4 => (2 : ℝ)) 2 f)
    (factorialCellMean (fun _ : Fin 4 => (3 : ℝ)) 3 f)
    ∂(cellAssignment fun _ => 1)) = 1 := by
  rw [integral_mainEffectB _ _ _ _ _ (fun _ => one_pos) (by decide)]
  simp only [popMean_const_fin4, mainEffectB]
  norm_num

/-- Interaction unbiasedness applied to the constant nonadditive fixture
(interaction `1`). -/
example : (∫ f, interactionAB (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 0 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 1 f)
    (factorialCellMean (fun _ : Fin 4 => (0 : ℝ)) 2 f)
    (factorialCellMean (fun _ : Fin 4 => (1 : ℝ)) 3 f)
    ∂(cellAssignment fun _ => 1)) = 1 := by
  rw [integral_interactionAB _ _ _ _ _ (fun _ => one_pos) (by decide)]
  simp only [popMean_const_fin4, interactionAB]
  norm_num

end MathlibExtTest.Probability.Statistics.Experiment
