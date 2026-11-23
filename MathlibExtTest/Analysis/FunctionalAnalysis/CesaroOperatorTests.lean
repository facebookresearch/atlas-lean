/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.CesaroOperator

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.CesaroOperatorTest

open MathlibExt.Analysis.FunctionalAnalysis.CesaroOperator

/-- The Cesàro operator is zero on the zero vector. -/
example : cesaroCLM (𝕜 := ℝ) 0 = 0 :=
  map_zero _

/-- The Cesàro operator applied to `e₀` at `0` is `1`. -/
example : cesaroCLM (𝕜 := ℝ) cesaroE0 0 = 1 := by
  rw [cesaroCLM_apply]
  simp [cesaroE0_apply]

/-- The Cesàro operator applied to `e₀` at `1` is `1 / 2`. -/
example : cesaroCLM (𝕜 := ℝ) cesaroE0 1 = 1 / 2 :=
  cesaroCLM_e0_apply_one

/-- Operator-norm bound: `‖C‖ ≤ 2`. -/
example : ‖cesaroCLM (𝕜 := ℝ)‖ ≤ 2 :=
  norm_cesaroCLM_le

/-- Operator-norm lower bound: `1 ≤ ‖C‖`. -/
example : 1 ≤ ‖cesaroCLM (𝕜 := ℝ)‖ :=
  one_le_norm_cesaroCLM

/-- The Cesàro operator on real `ℓ²` is injective. -/
example : Function.Injective (cesaroCLM (𝕜 := ℝ)) :=
  cesaroCLM_injective

/-- The alternating sequence `(-1)^n / (n + 1)` is not in the range of `C`. -/
example : cesaroNonRange (𝕜 := ℝ) ∉ Set.range (cesaroCLM (𝕜 := ℝ)) :=
  notMem_range_cesaroCLM

/-- The adjoint fixes `e₀`. -/
example : ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := ℝ)) cesaroE0 = cesaroE0 :=
  cesaro_adjoint_single_zero

/-- The adjoint applied to `e₀` at `1` is `0`: the adjoint is a tail sum. -/
example : ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := ℝ)) cesaroE0 1 = 0 := by
  rw [cesaro_adjoint_single_zero, cesaroE0_apply]
  simp

/-- The Cesàro operator on real `ℓ²` is not self-adjoint. -/
example : ¬ IsSelfAdjoint (cesaroCLM (𝕜 := ℝ)) :=
  not_isSelfAdjoint_cesaroCLM

/-- The Cesàro operator on real `ℓ²` is not compact. -/
example : ¬ IsCompactOperator (cesaroCLM (𝕜 := ℝ)) :=
  not_isCompactOperator_cesaroCLM

/-- The test vector with `N = 4` is a unit vector. -/
example : ‖cesaroTest (𝕜 := ℝ) 4‖ = 1 :=
  norm_cesaroTest 4 (by norm_num)

/-- The test vector with `N = 4` has coordinate `0` equal to `(√4)⁻¹`. -/
example : cesaroTest (𝕜 := ℝ) 4 0 = ((Real.sqrt 4 : ℝ) : ℝ)⁻¹ :=
  cesaroTest_apply 4 0

/-- `C` applied to the test vector with `N = 4` at coordinate `0` is `(√4)⁻¹`. -/
example : cesaroCLM (𝕜 := ℝ) (cesaroTest 4) 0 = ((Real.sqrt 4 : ℝ) : ℝ)⁻¹ :=
  cesaroCLM_test_apply_lt (by norm_num)

/-- `C` applied to the test vector with `N = 4` at coordinate `5` is
`4 (√4)⁻¹ / (5 + 1)`. -/
example : cesaroCLM (𝕜 := ℝ) (cesaroTest 4) 5
    = (4 : ℝ) * ((Real.sqrt 4 : ℝ) : ℝ)⁻¹ / (((5 : ℕ) : ℝ) + 1) :=
  cesaroCLM_test_apply_ge (𝕜 := ℝ) (by norm_num : (4 : ℕ) ≤ 5)

/-- The squared norm of `C` applied to the test vector with `N = 4` is at
least `5 / 4`. -/
example : (5 : ℝ) / 4 ≤ ‖cesaroCLM (𝕜 := ℝ) (cesaroTest 4)‖ ^ 2 :=
  five_div_four_le_norm_sq_cesaro_test 4 (by norm_num)

end MathlibExt.Analysis.FunctionalAnalysis.CesaroOperatorTest
