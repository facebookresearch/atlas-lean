/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541
import Mathlib.Data.Fintype.Powerset

/-!
# Tests for Erdős Problem 541

The hypotheses in these examples are checked by enumerating the subsets of the small index sets.
-/

open MathlibExt.Combinatorics.ZeroSumFixedLengthTwoResiduesErdosProblem541Wanted

-- The mixed sequence (1, 1, 1, 3, 3) has zero-sums of length three, and no other length.
private def mixed (i : Fin 5) : ZMod 5 := if i.val < 3 then 1 else 3

example : (Set.range mixed).ncard ≤ 2 :=
  fixedZeroSumLengthTwoResidues_holds 5 (by decide) mixed ⟨3, by decide⟩

example : ∑ i ∈ ({0, 1, 3} : Finset (Fin 5)), mixed i = 0 := by decide

-- The sole nonempty zero-sum is the singleton at index zero.
private def withZero (i : Fin 5) : ZMod 5 := if i = 0 then 0 else 1

example : (Set.range withZero).ncard ≤ 2 :=
  fixedZeroSumLengthTwoResidues_holds 5 (by decide) withZero ⟨1, by decide⟩

-- At the other endpoint, the full set is the only nonempty zero-sum.
example : (Set.range (fun _ : Fin 5 ↦ (1 : ZMod 5))).ncard ≤ 2 :=
  fixedZeroSumLengthTwoResidues_holds 5 (by decide) (fun _ ↦ 1) ⟨5, by decide⟩

-- The field of two elements is included in the public statement.
example : (Set.range (fun i : Fin 2 ↦ (i.val : ZMod 2))).ncard ≤ 2 :=
  fixedZeroSumLengthTwoResidues_holds 2 (by decide) (fun i ↦ i.val) ⟨1, by decide⟩
