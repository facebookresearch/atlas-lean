/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.FlowShop
meta import CSLibExt.Computability.Complexity.Karp.FlowShop.Verifier

/-! Tests for encoded three-machine flow-shop schedules. -/

namespace MetaMathlibExt.Complexity.NPComplete.FlowShop.Tests

open BitstringEncoding

private def checks (i : FlowShopInstance) (starts : List (List ℕ)) : Bool :=
  flowShopCheck (bitEncode i) (bitEncode starts)

-- The empty schedule and a schedule that finishes exactly at the deadline.
#guard checks ([], 0) []
#guard checks ([[1, 1, 1], [1, 1, 1]], 4) [[0, 1, 2], [1, 2, 3]]
#guard !(checks ([[1, 1, 1], [1, 1, 1]], 3) [[0, 1, 2], [1, 2, 3]])
#guard !(checks ([[1, 1, 1]], 3) [[0, 0, 2]])

-- Simultaneous positive operations and a zero-time operation inside a positive one.
#guard !(checks ([[1, 1, 1], [1, 1, 1]], 3) [[0, 1, 2], [0, 1, 2]])
#guard !(checks ([[0, 4, 0], [0, 0, 0]], 4) [[0, 0, 4], [0, 2, 4]])
#guard checks ([[0, 4, 0], [0, 0, 0]], 4) [[0, 0, 4], [0, 4, 4]]

-- Malformed bitstrings, malformed job rows, and malformed certificates.
#guard !(flowShopCheck [true] [])
#guard !(flowShopCheck (bitEncode (([], 0) : FlowShopInstance)) [true])
#guard !(checks ([[1, 1]], 3) [[0, 1, 2]])
#guard !(checks ([[1, 1, 1]], 3) [[0, 1]])
#guard !(checks ([[1, 1, 1]], 3) [])
#guard !(checks ([], 0) [[0, 0, 0]])

-- The total natural-number decoder also accepts this alternate encoding of the deadline 2.
#guard flowShopCheck (delimit (bitEncode ([[0, 2, 0]] : List (List ℕ))) ++ [false])
  (bitEncode ([[0, 0, 2]] : List (List ℕ)))

example : flowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
    ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ MetaMathlibExt.ComplexityTheory.NP →
        Cslib.CookLevin.PolyManyOneRed L flowShopDec :=
  flowShop_npComplete

end MetaMathlibExt.Complexity.NPComplete.FlowShop.Tests
