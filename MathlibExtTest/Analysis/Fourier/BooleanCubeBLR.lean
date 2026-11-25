/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeBLR
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open BooleanCube
open scoped BigOperators

/-! ### The BLR linearity test -/

/-- A character passes the BLR test with probability one. -/
example (S : Finset (Fin 3)) : blrAcceptProb (cubeChi 3 S) = 1 := by
  simp [blrAcceptProb, cubeChi_cubeMul]

/-- The Fourier form of the acceptance probability, on a character: `1/2 + 1/2 · 1 = 1`. -/
example (S : Finset (Fin 3)) :
    blrAcceptProb (cubeChi 3 S) = 1 / 2 + 1 / 2 * ∑ T, boolFourierCoeff 3 (cubeChi 3 S) T ^ 3 :=
  blrAcceptProb_eq (cubeChi_eq_one_or_neg_one S)

/-- The distance from a character to itself is zero. -/
example (S : Finset (Fin 3)) : boolDist (cubeChi 3 S) (cubeChi 3 S) = 0 := by
  simp [boolDist]

/-- The distance from a character to a different one is `1/2`. -/
example : boolDist (cubeChi 2 {0}) (cubeChi 2 {1}) = 1 / 2 := by
  rw [boolDist_cubeChi_eq (cubeChi_eq_one_or_neg_one _), boolFourierCoeff_cubeChi]
  norm_num

/-- The BLR conclusion for a function accepted with probability one: it is a character. -/
example (S : Finset (Fin 3)) : ∃ T, boolDist (cubeChi 3 S) (cubeChi 3 T) ≤ 0 :=
  blr_test (cubeChi_eq_one_or_neg_one S) (by simp [blrAcceptProb, cubeChi_cubeMul])

/-- The BLR theorem applies to an arbitrary `±1` function with a nontrivial threshold. -/
example (f : BoolCube 5 → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1) (h : 9 / 10 ≤ blrAcceptProb f) :
    ∃ S, boolDist f (cubeChi 5 S) ≤ 1 / 10 :=
  blr_test hf (by linarith)
