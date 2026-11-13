/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GaussianConcentration

import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory

/-- Boundary check: the tail bound instantiates for the identity
coefficient vector in dimension `1`, and the zero-vector event is
empty. -/
example : (Measure.pi fun _ => gaussianReal 0 1)
      {x : Fin 1 → ℝ | (1 : ℝ) ≤ |∑ i, (1 : Fin 1 → ℝ) i * x i|} ≤
    ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) ^ 2 / (2 * ∑ i, (1 : Fin 1 → ℝ) i ^ 2))) ∧
    (Measure.pi fun _ => gaussianReal 0 1)
      {x : Fin 1 → ℝ | (1 : ℝ) ≤ |∑ i, (0 : Fin 1 → ℝ) i * x i|} = 0 :=
  ⟨ProbabilityTheory.gaussian_linear_tail _ (by norm_num) (by norm_num [Finset.sum]),
   ProbabilityTheory.gaussian_linear_tail_zero _ (by norm_num) (by simp)⟩
