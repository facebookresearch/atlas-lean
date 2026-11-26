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

-- Simultaneous positive operations and a zero-time operation inside a positive one.
#guard !(checks ([[1, 1, 1], [1, 1, 1]], 3) [[0, 1, 2], [0, 1, 2]])
#guard !(checks ([[0, 4, 0], [0, 0, 0]], 4) [[0, 0, 4], [0, 2, 4]])
#guard checks ([[0, 4, 0], [0, 0, 0]], 4) [[0, 0, 4], [0, 4, 4]]

-- The deadline forces the second job's zero-duration operation strictly inside the first job.
example : ¬ FlowShopFeasible ([[0, 2, 0], [1, 0, 1]], 2) := by
  rintro ⟨s, _, _, jobs, machines⟩
  let a := s.getD 0 []
  let b := s.getD 1 []
  have a₂ : a.getD 1 0 + 2 ≤ a.getD 2 0 := (jobs 0 (by decide)).2.1
  have a₃ : a.getD 2 0 + 0 ≤ 2 := (jobs 0 (by decide)).2.2
  have b₁ : b.getD 0 0 + 1 ≤ b.getD 1 0 := (jobs 1 (by decide)).1
  have b₂ : b.getD 1 0 + 0 ≤ b.getD 2 0 := (jobs 1 (by decide)).2.1
  have b₃ : b.getD 2 0 + 1 ≤ 2 := (jobs 1 (by decide)).2.2
  have sep : a.getD 1 0 + 2 ≤ b.getD 1 0 ∨ b.getD 1 0 + 0 ≤ a.getD 1 0 :=
    machines 1 (by decide) 0 (by decide) 1 (by decide) (by decide)
  omega

-- Malformed bitstrings, malformed job rows, and malformed certificates.
#guard !(flowShopCheck [true] [])
#guard !(checks ([[1, 1]], 3) [[0, 1, 2]])
#guard !(checks ([[1, 1, 1]], 3) [[0, 1]])
#guard !(checks ([[1, 1, 1]], 3) [])

-- The total natural-number decoder also accepts this alternate encoding of the deadline 2.
#guard flowShopCheck (delimit (bitEncode ([[0, 2, 0]] : List (List ℕ))) ++ [false])
  (bitEncode ([[0, 0, 2]] : List (List ℕ)))

example : flowShopDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
    ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ MetaMathlibExt.ComplexityTheory.NP →
        Cslib.CookLevin.PolyManyOneRed L flowShopDec :=
  flowShop_npComplete

end MetaMathlibExt.Complexity.NPComplete.FlowShop.Tests
