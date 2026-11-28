/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDyadicIdentities

/-! # Tests for dyadic normalization, D-node counts and binary digit sums -/

open MetaMathlibExt

-- The smallest positive integer has exponent zero and mantissa zero.
example (x : ℚ) (hx : 1 = 1 + x) : x = 0 := by
  simpa using (dyadic_mantissa_eq 1 0 0 x (by decide) rfl (by simpa using hx)).1

-- Immediately below eight, the remainder three gives the nonintegral mantissa 3/4.
example (x : ℚ) (hx : 7 = 4 * (1 + x)) : x = 3 / 4 ∧ 1 + x = 7 / 4 :=
  dyadic_mantissa_eq 7 2 3 x (by decide) rfl hx

-- The stipulated value at zero agrees with the count for a single leaf.
example : dcDNodes 0 = 0 ∧ dcDNodes 1 = 0 :=
  ⟨by decide +kernel, dcDNodes_one⟩

-- The raw difference goes from positive to negative across a power of two.
example : (dcDNodes 7 : ℚ) - dcDNodes 8 = 2 := by
  have h := hammingWeight_eq_dcDNodes_diff 7 (by decide)
  rw [show (Nat.digits 2 7).sum = 3 by decide, show Nat.log 2 7 = 2 by decide] at h
  linarith only [h]

example : (dcDNodes 8 : ℚ) - dcDNodes 9 = -3 := by
  have h := hammingWeight_eq_dcDNodes_diff 8 (by decide)
  rw [show (Nat.digits 2 8).sum = 1 by decide, show Nat.log 2 8 = 3 by decide] at h
  linarith only [h]

-- The largest offset below the next power of two is odd, so the correction is +1.
example : (dcDNodes 7 : ℚ) - ((dcDNodes 6 : ℚ) + dcDNodes 8) / 2 = 1 := by
  have h := dcDNodes_eq_midpoint_add_one_sub_lowestBit 2 3 (by decide) (by decide)
  change (dcDNodes 7 : ℚ) = ((dcDNodes 6 : ℚ) + dcDNodes 8) / 2 + 1 - padicValNat 2 3 at h
  rw [show padicValNat 2 3 = 0 by decide +kernel, Nat.cast_zero, sub_zero] at h
  linarith only [h]

-- The offset four has valuation two, so the correction is -1.
example : (dcDNodes 12 : ℚ) - ((dcDNodes 11 : ℚ) + dcDNodes 13) / 2 = -1 := by
  have h := dcDNodes_eq_midpoint_add_one_sub_lowestBit 3 4 (by decide) (by decide)
  change (dcDNodes 12 : ℚ) = ((dcDNodes 11 : ℚ) + dcDNodes 13) / 2 + 1 - padicValNat 2 4 at h
  rw [show padicValNat 2 4 = 2 by decide +kernel, Nat.cast_ofNat] at h
  linarith only [h]

-- At level two, the count rises and then falls as bit two changes from zero to one at 12 leaves.
example : dcLevelDNodes 11 2 = 3 ∧ dcLevelDNodes 12 2 = 4 ∧ dcLevelDNodes 13 2 = 3 := by decide

-- With three leaves, the root has unequal subtrees and its sole interior child has equal ones.
example :
    let t : BinaryTree Unit := .node () .nil (.node () .nil .nil)
    IsDivideConquerTree t ∧ treeDNodes t = 1 ∧ treeSNodes t = 1 := by
  simp [IsDivideConquerTree, treeDNodes, treeSNodes, BinaryTree.numLeaves]

-- A single leaf has no interior nodes.
example : treeDNodes .nil = 0 := by
  rw [treeDNodes_eq_numLeaves_sub_one_sub_treeSNodes]
  decide

-- The root is an S-node: the mirrored subtrees have the same number of leaves.
example :
    let t : BinaryTree Unit := .node () (.node () .nil (.node () .nil .nil))
      (.node () (.node () .nil .nil) .nil)
    treeDNodes t = 2 := by
  dsimp only
  rw [treeDNodes_eq_numLeaves_sub_one_sub_treeSNodes]
  decide

-- In the four-leaf comb, the top two nodes are D-nodes.
example : treeDNodes (.node () .nil (.node () .nil (.node () .nil .nil))) = 2 := by
  rw [treeDNodes_eq_numLeaves_sub_one_sub_treeSNodes]
  decide

open Finset

private def levelSum (n : ℕ) : ℕ := ∑ i ∈ range (Nat.log 2 n), dcLevelDNodes n i

private def signedLevelSum (n : ℕ) : ℤ :=
  ∑ i ∈ range (Nat.log 2 n),
    (↑(n / 2 ^ i % 2) * (2 : ℤ) ^ i + (-1) ^ (n / 2 ^ i % 2) * ↑(n % 2 ^ i))

-- One leaf has no interior levels, so both sums are empty.
example : dcDNodes 1 = 0 ∧ levelSum 1 = 0 ∧ signedLevelSum 1 = 0 := by decide +kernel

-- At five and six leaves, the total is the same, but the two levels contribute differently.
example :
    dcDNodes 5 = 2 ∧ dcLevelDNodes 5 0 = 1 ∧ dcLevelDNodes 5 1 = 1 ∧
      levelSum 5 = 2 ∧ signedLevelSum 5 = 2 := by decide +kernel

example :
    dcDNodes 6 = 2 ∧ dcLevelDNodes 6 0 = 0 ∧ dcLevelDNodes 6 1 = 2 ∧
      levelSum 6 = 2 ∧ signedLevelSum 6 = 2 := by decide +kernel

-- Seven leaves split into three and four. At eight leaves every split is even.
example : dcDNodes 7 = 2 ∧ levelSum 7 = 2 ∧ signedLevelSum 7 = 2 := by decide +kernel

example : dcDNodes 8 = 0 ∧ levelSum 8 = 0 ∧ signedLevelSum 8 = 0 := by decide +kernel

example : dcDNodes 7 = levelSum 7 ∧ (dcDNodes 7 : ℤ) = signedLevelSum 7 :=
  dcDNodes_eq_sum_dcLevelDNodes 7 (by decide)
