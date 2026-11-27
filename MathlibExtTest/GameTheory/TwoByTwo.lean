/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.TwoByTwo

/-! # Tests for the two-by-two bimatrix classification -/

namespace MathlibExtTest.GameTheory.TwoByTwo

open Convexity MathlibExt.GameTheory.TwoByTwo MathlibExt.GameTheory.LemkeHowsonWanted

private abbrev Payoffs := Fin 2 → Fin 2 → ℝ

private def coordA : Payoffs := ![![5, 1], ![3, 2]]
private def coordB : Payoffs := ![![7, 4], ![1, 3]]
private def antiA : Payoffs := ![![1, 5], ![4, 3]]
private def antiB : Payoffs := ![![3, 4], ![6, 2]]

variable (x y : StdSimplex ℝ (Fin 2))

-- A test directly in interval coordinates: swapping players or transposing B changes the set.
example (p q : Set.Icc (0 : ℝ) 1) :
    IsBimatrixNash coordA coordB (firstProbEquiv.symm p) (firstProbEquiv.symm q) ↔
      ((p : ℝ) = 2 / 5 ∧ (q : ℝ) = 1 / 3) ∨
      ((p : ℝ) = 1 ∧ (q : ℝ) = 1) ∨ ((p : ℝ) = 0 ∧ (q : ℝ) = 0) := by
  rw [isBimatrixNash_iff_of_crossing] <;> norm_num [rowGap, colGap, coordA, coordB]

-- Reversing the sign pattern of both players changes exactly which two corners are equilibria.
example : IsBimatrixNash antiA antiB x y ↔
    (x.weights 0 = 4 / 5 ∧ y.weights 0 = 2 / 5) ∨
    (x.weights 0 = 1 ∧ y.weights 0 = 0) ∨ (x.weights 0 = 0 ∧ y.weights 0 = 1) := by
  rw [isBimatrixNash_iff_of_crossing] <;> norm_num [rowGap, colGap, antiA, antiB]

-- Matching pennies: the uniform pair is the entire equilibrium set, not just one witness.
private def pennies : Payoffs := ![![1, -1], ![-1, 1]]

example : IsBimatrixNash pennies (fun i j => -pennies i j) x y ↔
    x.weights 0 = 1 / 2 ∧ y.weights 0 = 1 / 2 := by
  rw [isBimatrixNash_iff_of_crossing] <;> norm_num [rowGap, colGap, pennies]

-- The first player strictly prefers bottom; the second chooses left against bottom.
private def preferBottom : Payoffs := ![![1, 5], ![2, 9]]

example : IsBimatrixNash preferBottom antiB x y ↔ x.weights 0 = 0 ∧ y.weights 0 = 1 := by
  rw [isBimatrixNash_iff_of_row_dominance] <;> norm_num [rowGap, colGap, preferBottom, antiB]

-- The second player strictly prefers right; the first chooses top against right.
private def preferRight : Payoffs := ![![4, 9], ![3, 6]]

example : IsBimatrixNash antiA preferRight x y ↔ y.weights 0 = 0 ∧ x.weights 0 = 1 := by
  rw [isBimatrixNash_iff_of_col_dominance] <;> norm_num [rowGap, colGap, antiA, preferRight]

-- In a constant game even arbitrary, independently chosen real probabilities are permitted.
example (p q : Set.Icc (0 : ℝ) 1) :
    IsBimatrixNash (fun _ _ => 3) (fun _ _ => 3) (firstProbEquiv.symm p) (firstProbEquiv.symm q) :=
  isBimatrixNash_const _ _ _ _

-- Against left, the row player is indifferent. Nonetheless only part of this edge is Nash:
-- the column player requires 2p − (1−p) ≥ 0. The threshold itself is included.
private def tieA : Payoffs := ![![5, 1], ![5, 3]]
private def tieB : Payoffs := ![![6, 4], ![2, 3]]

example : IsBimatrixNash tieA tieB x (StdSimplex.single 0) ↔ 1 / 3 ≤ x.weights 0 := by
  rw [isBimatrixNash_iff]
  norm_num [rowGap, colGap, tieA, tieB, Finsupp.single_apply]
  constructor <;> intro h <;> linarith

end MathlibExtTest.GameTheory.TwoByTwo
