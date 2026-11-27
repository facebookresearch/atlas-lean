/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsackHardness
public import CSLibExt.Computability.Complexity.Basic

/-! # Tests for the SUBSET-SUM to MULTIPLE KNAPSACK machine -/

open MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
open MetaMathlibExt.BitstringEncoding Cslib.Complexity Cslib.Complexity.Karp

-- The machine theorem and the answer-preservation theorem give the many-one reduction.
example : PolyManyOneRed subsetSumDec multipleKnapsackDec :=
  ⟨reduceFromSubsetSum, HardnessMachine.isPolyTime_reduceFromSubsetSum,
    reduceFromSubsetSum_correct⟩

-- Polynomial-time maps compose: running the reduction twice is again polynomial-time.
example : MetaMathlibExt.ComplexityTheory.IsPolyTime (reduceFromSubsetSum ∘ reduceFromSubsetSum) :=
  MetaMathlibExt.ComplexityTheory.IsPolyTime.comp
    HardnessMachine.isPolyTime_reduceFromSubsetSum
    HardnessMachine.isPolyTime_reduceFromSubsetSum

-- The computed map on a canonical source, and on a noncanonical one (a final false bit).
example : reduceFromSubsetSum (encodeSS [1, 0] 1) = bitEncode (fromSubsetSum [1, 0] 1) := by
  decide

example : reduceFromSubsetSum [true, false, false] = bitEncode noInstance := by decide
