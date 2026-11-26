/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantUpperBoundErdosUnpublishedFourNinthsHolds
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundErdosUnpublishedFourNinthsHolds

example : C₁ᵦ ≤ (4 : ℝ) / 9 := upperBound_Erdos_unpublished_fourNinths_holds

example : C₁ᵦ < (1 : ℝ) / 2 :=
  lt_of_le_of_lt upperBound_Erdos_unpublished_fourNinths_holds (by norm_num)

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundErdosUnpublishedFourNinthsHolds
