/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteExponentialFamily
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Tests for finite exponential families

The Bernoulli family on `Bool` with statistic `φ true = 1`, `φ false = 0` over `E = ℝ`:
`A(θ) = log (1 + e^θ)` (softplus) and `∇A(θ) = e^θ / (1 + e^θ)` (logistic sigmoid).
-/

@[expose] public section

open Real MathlibExt.Probability.FiniteExponentialFamily

namespace MathlibExtTest.FiniteExponentialFamily

/-- Bernoulli sufficient statistic. -/
def φ : Bool → ℝ := fun b => if b then 1 else 0

theorem partitionSum_bernoulli (θ : ℝ) : partitionSum φ θ = exp θ + 1 := by
  simp [partitionSum, φ, add_comm]

example : logPartition φ 0 = log 2 := by
  rw [logPartition, partitionSum_bernoulli]; norm_num

example : meanParameter φ 0 = 1 / 2 := by
  simp [meanParameter, density, partitionSum_bernoulli, φ]
  norm_num

/-- The gradient of softplus is the sigmoid, as an instance of `hasGradientAt_logPartition`. -/
example (θ : ℝ) : HasGradientAt (logPartition φ) (meanParameter φ θ) θ :=
  hasGradientAt_logPartition φ θ

example : ConvexOn ℝ Set.univ (logPartition φ) := convexOn_logPartition φ

/-- The variational principle at the uniform distribution and `θ = 0`: `log 2 ≤ log 2`. -/
example : ∑ x : Bool, (1 / 2 : ℝ) * (inner ℝ (φ x) 0 - log (1 / 2)) ≤ logPartition φ 0 :=
  sum_mul_inner_sub_log_le φ 0 (fun _ => by norm_num) (by norm_num)

end MathlibExtTest.FiniteExponentialFamily
