/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsackComplete
public import CSLibExt.Computability.Complexity.Consequences

/-! # Consumers of the NP-completeness of MULTIPLE KNAPSACK -/

open MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
open Cslib.Complexity Cslib.Complexity.Karp

example : NPComplete multipleKnapsackDec :=
  npComplete_iff.mpr multipleKnapsack_npComplete

-- SUBSET-SUM and MULTIPLE KNAPSACK reduce to each other.
example : PolyManyOneRed subsetSumDec multipleKnapsackDec :=
  multipleKnapsack_npComplete.2 _ subsetSumDec_mem_NP

example : PolyManyOneRed multipleKnapsackDec subsetSumDec :=
  subsetSumDec_npHard _ multipleKnapsack_npComplete.1

-- A polynomial-time algorithm for MULTIPLE KNAPSACK would give P = NP.
example (h : multipleKnapsackDec ∈ P) : P = NP :=
  (npComplete_iff.mpr multipleKnapsack_npComplete).P_eq_NP h
