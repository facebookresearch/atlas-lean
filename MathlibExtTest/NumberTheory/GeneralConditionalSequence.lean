/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralConditionalSequence
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Tests for generating functions of decimated sequences
-/

open MetaMathlibExt PowerSeries

-- The second correction uses the two highest-index coefficients in descending order.
example (A s : ℕ → ℤ) :
    decimationCoeff A s 3 2 2 1 = s 5 - (A 2 * s 3 + A 1 * s 1) := by
  simp [decimationCoeff, Finset.sum_range_succ]

-- For sₙ = n, the two residue classes contribute 2X² and X + X³.
example :
    mk (fun n : ℕ ↦ (n : ℤ)) * (1 - (2 * X ^ 2 - X ^ 4)) =
      2 * X ^ 2 + X + X ^ 3 := by
  let A (j : ℕ) : ℤ := if j = 0 then -1 else 2
  have hrec (n : ℕ) :
      ((n + 2 * 2 : ℕ) : ℤ) = ∑ j ∈ Finset.range 2, A j * ((n + j * 2 : ℕ) : ℤ) := by
    simp [Finset.sum_range_succ, A]
    ring
  have h := decimation_generating_function (s := fun n ↦ (n : ℤ)) (m := 2) (r := 2) hrec
  norm_num [decimationCoeff, Finset.sum_range_succ, A] at h
  convert h using 1 <;> ring

-- At stride zero, the nonzero denominator 1 - 3 annihilates the constant sequence 3 in ℤ/6ℤ.
example : mk (fun _ ↦ (3 : ZMod 6)) * (1 - C 3) = 0 := by
  simpa using decimation_generating_function (m := 1) (r := 0)
    (A := fun _ ↦ (3 : ZMod 6)) (s := fun _ ↦ 3) (by
      intro n
      simp only [Finset.sum_range_one]
      decide)
