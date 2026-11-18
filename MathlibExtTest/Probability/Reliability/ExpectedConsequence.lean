/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.ExpectedConsequence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Expected-consequence checks

Focused checks for
`MathlibExt.Probability.Reliability.ExpectedConsequence`: the
two-damage-state form of the decomposition, and monotonicity
applied at concrete losses.

These are elaboration and non-vacuity checks, not new results.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Two damage states: the state sum has two terms. -/
example (κ : ProbabilityTheory.Kernel PUnit (Fin 2))
    (μ : Measure PUnit) (L : Fin 2 → ℝ≥0∞) :
    expectedConsequence κ μ L
      = ∫⁻ a, ((κ a {0}) * L 0 + (κ a {1}) * L 1) ∂μ := by
  rw [expectedConsequence_fintype]
  exact lintegral_congr fun a => by rw [Fin.sum_univ_two]

/-- Monotonicity at concrete losses. -/
example (κ : ProbabilityTheory.Kernel PUnit (Fin 2))
    (μ : Measure PUnit) :
    expectedConsequence κ μ (fun _ => 1)
      ≤ expectedConsequence κ μ (fun _ => 7) :=
  expectedConsequence_mono κ μ (fun _ => by norm_num)
