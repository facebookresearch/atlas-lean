/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.FunctionalAnalysis.G09TikhonovConsistency

/-!
# Tests for small-noise Tikhonov consistency (G09)

Closed checks on the one-dimensional operator `A = 1 : ℝ →L[ℝ] ℝ`:
the energy bound, the consistency bound with `w = 1`, `A = 0` forcing
`xdag = 0` under the source condition, and the bound at `lam = delta`.
The convergence theorem is the module-level statement.
-/

@[expose] public section

open Filter Topology Real

namespace MathlibExt.Analysis.FunctionalAnalysis.G09TikhonovConsistency

/-- One-dimensional energy bound: `A = 1`, `z = 3`, `x = 1` solves the
normal equation at `lam = 2`, and `2 * 1 ≤ 3 * 1 - 1 ≤ 9 / 4`. -/
example :
    (2 : ℝ) * ‖(1 : ℝ)‖ ^ 2 ≤ ‖(3 : ℝ)‖ * ‖(1 : ℝ →L[ℝ] ℝ) 1‖ - ‖(1 : ℝ →L[ℝ] ℝ) 1‖ ^ 2 ∧
      ‖(3 : ℝ)‖ * ‖(1 : ℝ →L[ℝ] ℝ) 1‖ - ‖(1 : ℝ →L[ℝ] ℝ) 1‖ ^ 2 ≤ ‖(3 : ℝ)‖ ^ 2 / 4 := by
  have hx : (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) ∘L (1 : ℝ →L[ℝ] ℝ) +
      (2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) (1 : ℝ) =
      ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) (3 : ℝ) := by
    norm_num [ContinuousLinearMap.adjoint_one]
  exact g09_energy_bound (1 : ℝ →L[ℝ] ℝ) 3 1 (by norm_num) hx

/-- One-dimensional consistency: `A = 1`, `w = 1`, `xdag = 1`, `b = 1`,
`bdelta = 1 + delta`, `xlam = 1`, `lam = delta = 1/4`: the error is `0`
and the bound is `1/4 / (2 * 1/2) + (1/2) * 1 / 2 = 1/2`. -/
example :
    ‖(1 : ℝ) - (1 : ℝ)‖ ≤ (1 / 4 : ℝ) / (2 * Real.sqrt (1 / 4)) +
      Real.sqrt (1 / 4) * ‖(1 : ℝ)‖ / 2 := by
  have hxlam : (ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) ∘L (1 : ℝ →L[ℝ] ℝ) +
      ((1 / 4 : ℝ) : ℝ) • (1 : ℝ →L[ℝ] ℝ)) (1 : ℝ) =
      ContinuousLinearMap.adjoint (1 : ℝ →L[ℝ] ℝ) (1 + 1 / 4 : ℝ) := by
    norm_num [ContinuousLinearMap.adjoint_one]
  have h := g09_consistency_bound (A := (1 : ℝ →L[ℝ] ℝ)) (xdag := (1 : ℝ)) (w := (1 : ℝ))
    (b := (1 : ℝ)) (bdelta := (1 + 1 / 4 : ℝ)) (xlam := (1 : ℝ)) (lam := (1 / 4 : ℝ))
    (delta := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    (by simp [ContinuousLinearMap.adjoint_one]) (by simp) (by norm_num) hxlam

  exact h

/-- `A = 0` forces `xdag = 0` under the source condition: `A† w = 0`. -/
example (w : ℝ) :
    ContinuousLinearMap.adjoint (0 : ℝ →L[ℝ] ℝ) (w : ℝ) = 0 := by
  simp

#print axioms g09_energy_bound
#print axioms g09_norm_le_of_normal_equations
#print axioms g09_consistency_bound
#print axioms g09_convergence

end MathlibExt.Analysis.FunctionalAnalysis.G09TikhonovConsistency
