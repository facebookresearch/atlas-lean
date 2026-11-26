/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantUpperBoundGGSWT2025AlphaEvolveHolds
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundGGSWT2025AlphaEvolveHolds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : upperBound_GGSWT2025_AlphaEvolve = (C₁ᵦ ≤ (380924 : ℝ) / 1000000) := rfl

example : C₁ᵦ ≤ (380924 : ℝ) / 1000000 := upperBound_GGSWT2025_AlphaEvolve_holds

/-- The minimum-overlap constant is strictly below `381 / 1000`. -/
public theorem lt_381_div_1000 : C₁ᵦ < (381 : ℝ) / 1000 :=
  lt_of_le_of_lt upperBound_GGSWT2025_AlphaEvolve_holds (by norm_num)

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundGGSWT2025AlphaEvolveHolds
