/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.LinearQuadraticRegulator
import Mathlib.Algebra.Order.Star.Real

open Matrix

namespace CSLibExt.MachineLearning.LinearQuadraticRegulator

-- One step from zero terminal cost: the Riccati update of `0` is `Q`.
example (A Q : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ)
    (R : Matrix (Fin 1) (Fin 1) ℝ) :
    riccatiMap A B Q R 0 = Q := by
  simp [riccatiMap]

-- The scalar integrator `x_{t+1} = x_t + u_t` with unit costs: every control sequence over three
-- steps costs at least the Riccati value, and the linear feedback attains it.
example (x₀ : Fin 1 → ℝ) (u : ℕ → Fin 1 → ℝ) :
    x₀ ⬝ᵥ (riccatiCostToGo (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 3 *ᵥ x₀) ≤
      lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 x₀ u 3 :=
  lqrCost_ge PosSemidef.one PosDef.one PosSemidef.zero 3 x₀ u

example (x₀ : Fin 1 → ℝ) : ∃ u : ℕ → Fin 1 → ℝ,
    lqrCost (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 x₀ u 3 =
      x₀ ⬝ᵥ (riccatiCostToGo (σ := Fin 1) (ι := Fin 1) 1 1 1 1 0 3 *ᵥ x₀) :=
  (lqrCost_feedback PosSemidef.one PosDef.one PosSemidef.zero 3 x₀).imp fun _ h => h.1

end CSLibExt.MachineLearning.LinearQuadraticRegulator
