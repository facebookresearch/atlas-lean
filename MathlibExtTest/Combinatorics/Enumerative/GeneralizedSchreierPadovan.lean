/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedSchreierPadovan
import Mathlib.Tactic.Ring

/-!
# Tests for Schreier counts and polynomial recurrences
-/

open Polynomial MetaMathlibExt

-- The coefficient of X multiplies the preceding term of the geometric sequence.
example : SatisfiesPoly ((X - C (1 / 2 : ℝ)) * (X + 1)) (fun n => 2 ^ n) := by
  apply SatisfiesPoly.of_dvd (P := X - C (1 / 2)) _ (dvd_mul_right _ _)
  rintro (_ | n) hn
  · simp at hn
  · simp [Finset.sum_range_succ, coeff_X, coeff_C, pow_succ]
    ring

-- The zero multiple has degree zero even if the original recurrence has positive degree.
example {P : Polynomial ℝ} {a : ℕ → ℝ} (h : SatisfiesPoly P a) : SatisfiesPoly 0 a :=
  h.of_dvd (dvd_zero P)

-- A nonzero constant recurrence already constrains the term of index zero.
example {a : ℕ → ℝ} (h : SatisfiesPoly 1 a) : a 0 = 0 := by
  simpa using h 0 (by simp)

-- The shift includes maximum zero, where the Schreier family is empty.
example {p : ℕ} (hp : 1 ≤ p) : maximalSchreierCount p 1 (p + 1) = 0 := by
  simpa [schreierCount, Finset.filter_singleton] using
    (schreierCount_eq_maximalSchreierCount_add hp 0).symm

-- At maximum five, both {5} and {4, 5} contribute to the shifted maximal count.
example : maximalSchreierCount 2 1 8 = 2 := by
  rw [← schreierCount_eq_maximalSchreierCount_add (p := 2) (by decide) 5]
  decide +kernel
