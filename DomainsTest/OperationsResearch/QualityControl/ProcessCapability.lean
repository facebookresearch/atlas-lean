/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.OperationsResearch.QualityControl.ProcessCapability
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.NormNum

/-! # Regressions for the population process capability indices -/

open MeasureTheory ProbabilityTheory OperationsResearch.QualityControl

-- Equal spread, but a one-unit shift from the midpoint lowers Cpk to 2/3.
example : processCapabilityIndices 7 13 10 1 = (1, 1) ∧
    processCapabilityIndices 7 13 11 1 = (1, (2 : ℝ) / 3) := by
  norm_num [processCapabilityIndices, min_def]

-- The midpoint identity still applies when the specification interval has zero width.
example : (processCapabilityIndices 10 10 11 1).1 = 0 ∧
    (processCapabilityIndices 10 10 11 1).2 ≤ 0 :=
  (processCapabilityIndices_midpoint (show (10 : ℝ) ≤ 10 by rfl)
    (show (0 : ℝ) < 1 by norm_num) (μ := 11)).2.2.2 rfl

-- A negative slope swaps the transformed endpoints; reversed original limits never pass.
example : {x : ℝ | 7 ≤ x ∧ x ≤ 13} = {x | 4 + (-2) * 13 ≤ 4 + (-2) * x ∧
    4 + (-2) * x ≤ 4 + (-2) * 7} ∧ {x : ℝ | 13 ≤ x ∧ x ≤ 7} = ∅ :=
  ⟨(processCapability_pass_events id 7 13 4 (-2)).2.1 (by norm_num),
    (processCapability_pass_events id 13 7 4 2).2.2 (by norm_num)⟩

-- Use actual population moments: recoding an off-center score preserves both indices.
example :
    let P := gaussianReal 11 1
    let Y := fun x : ℝ => -5 + 2 * x
    (∫ x, Y x ∂P) = 17 ∧ populationSD P Y = 2 ∧
      processCapabilityIndices 9 21 (∫ x, Y x ∂P) (populationSD P Y) = (1, (2 : ℝ) / 3) := by
  intro P Y
  have hmean : (∫ x : ℝ, x ∂P) = 11 := integral_id_gaussianReal
  have hsd : populationSD P id = 1 := by
    unfold populationSD P
    rw [variance_id_gaussianReal]
    norm_num
  have hpos : 0 < populationSD P id := by rw [hsd]; norm_num
  have h := processCapabilityIndices_affine_moments (P := P) (X := id)
    (memLp_id_gaussianReal 2) (show (7 : ℝ) ≤ 13 by norm_num) hpos (-5) (b := 2) (by norm_num)
  norm_num [hmean, hsd, processCapabilityIndices, min_def, Y] at h ⊢
  exact h
