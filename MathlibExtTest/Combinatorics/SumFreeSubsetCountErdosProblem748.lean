/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748
import Mathlib.Tactic.Linarith

/-! # Tests for `MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748` -/

namespace MathlibExtTest.SumFreeSubsetCountErdosProblem748

open MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748Wanted

-- Test section: small values. The empty set counts, so `f(0) = 1`.
example : sumFreeCount 0 = 1 := by decide

-- `{1}` is sum-free: `1 + 1 = 2` is not in it.
example : sumFreeCount 1 = 2 := by decide

-- `{1, 2}` is not sum-free, because `2 = 1 + 1` (the case `b = c` counts).
example : sumFreeCount 2 = 3 := by decide

-- Of the subsets of `{1, 2, 3}`, `{1, 2}` and `{1, 2, 3}` are not sum-free.
example : sumFreeCount 3 = 6 := by decide

example : sumFreeCount 5 = 16 := by decide

-- Test section: the limit. For every `ε > 0`, eventually `log₂ f(n) / n < 1 / 2 + ε`, that is,
-- `f(n) < 2 ^ ((1 / 2 + ε) n)`.
example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, Real.logb 2 (sumFreeCount n) / n < 1 / 2 + ε :=
  (tendsto_order.1 sumFreeCountExponent_holds).2 _ (by linarith)

-- ... and eventually `1 / 2 - ε < log₂ f(n) / n`.
example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, 1 / 2 - ε < Real.logb 2 (sumFreeCount n) / n :=
  (tendsto_order.1 sumFreeCountExponent_holds).1 _ (by linarith)

end MathlibExtTest.SumFreeSubsetCountErdosProblem748
