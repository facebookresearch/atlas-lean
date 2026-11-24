/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.LinearRandomResponse

/-!
# Tests for `PhyslibExt.Mechanics.LinearRandomResponse`

* the fixture `c = 2`, `k = 8`, `σ = 4`: rate `θ = 4`, noise amplitude `σ' = 2` and the nonzero
  stationary variance `σ² / (2 c k) = 1 / 2`;
* nonvacuity: a pathwise stationary response with these parameters exists, and its variance is
  `1 / 2` at every time.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.LinearRandomResponse

open MeasureTheory ProbabilityTheory _root_.Mechanics.LinearRandomResponse
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Fixture: `c = 2`, `k = 8`, `σ = 4` give the rate `θ = 4`, the noise amplitude `σ' = 2` and
the nonzero stationary variance `σ² / (2 c k) = 1 / 2`. -/
example {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck ((8 : ℝ) / 2) ((4 : ℝ) / 2) X P) (t : ℝ≥0) :
    Var[X t; P] = 1 / 2 := by
  rw [stationaryResponse_variance (c := 2) (k := 8) (σ := 4) (by norm_num) hX t]
  norm_num

/-- Nonvacuity: a pathwise stationary response with `c = 2`, `k = 8` and `σ = 4` exists, and its
variance is `1 / 2` at every time. -/
example : ∃ μ : Measure (ℝ≥0 → ℝ), ∃ X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
    IsStationaryOrnsteinUhlenbeck ((8 : ℝ) / 2) ((4 : ℝ) / 2) X μ ∧
      ∀ t, Var[X t; μ] = 1 / 2 := by
  obtain ⟨μ, B, X₀, -, -, -, -, hX⟩ :=
    exists_stationaryResponse (c := 2) (k := 8) (by norm_num) (by norm_num) 4
  refine ⟨μ, _, hX, fun t => ?_⟩
  rw [stationaryResponse_variance (c := 2) (k := 8) (σ := 4) (by norm_num) hX t]
  norm_num

end PhyslibExtTest.Mechanics.LinearRandomResponse
