/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosMinimumOverlapConstantUpperBoundYKLBMWKCZGS2026TTTDiscoverHolds
import Mathlib.Tactic.NormNum

/-! # Numerical consequences of the TTT-Discover upper bound

The TTT-Discover bound implies the strict upper bound `381 / 1000`.
-/

namespace MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundYKLBMWKCZGS2026TTTDiscoverHolds

open MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

example : C₁ᵦ < (381 : ℝ) / 1000 :=
  upperBound_YKLBMWKCZGS2026_TTTDiscover_holds.trans_lt (by norm_num)

end MathlibExtTest.NumberTheory.ErdosMinimumOverlapConstantUpperBoundYKLBMWKCZGS2026TTTDiscoverHolds
