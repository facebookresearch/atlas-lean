/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsackVerify

/-! # Tests for the MULTIPLE KNAPSACK verifier machine -/

open MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
open MetaMathlibExt.BitstringEncoding

-- The polynomial-time check and quadratic certificates put MULTIPLE KNAPSACK in NP.
example : multipleKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  ⟨Polynomial.X ^ 2, fun q => mkCheck q.1 q.2, Verify.isPolyTime_mkCheck, fun x => by
    rw [multipleKnapsackDec_iff_check]
    simp⟩

-- The machine computes the same answers as the pure check, for instance on these inputs.
example : mkCheck (bitEncode (([(2, 3), (1, 1)], [2, 1], 4) : MultipleKnapsackInstance))
    [true, false, false, true] = true := by decide

example : mkCheck (bitEncode (([(2, 3), (1, 1)], [2, 1], 5) : MultipleKnapsackInstance))
    [true, false, false, true] = false := by decide

-- No knapsacks: only the target value 0 is reachable, with the empty certificate.
example : mkCheck (bitEncode (([(2, 3)], [], 0) : MultipleKnapsackInstance)) [] = true := by
  decide

example : mkCheck (bitEncode (([(2, 3)], [], 1) : MultipleKnapsackInstance)) [true] = false := by
  decide
