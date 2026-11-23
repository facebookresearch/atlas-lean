/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.Interpolation.HermiteCubic

/-!
# Hermite cubic checks

Focused checks for `MathlibExt.Interpolation.HermiteCubic`: the
four unit basis data on `L = 2` through the public end-condition
theorems, and zero end data giving the zero cubic.

These are elaboration and non-vacuity checks, not new results.
-/

open HermiteCubic

/-- Each basis datum is realized, through the public theorems. -/
example : hermite 2 1 0 0 0 0 = 1 ∧ hermite 2 1 0 0 0 2 = 0
    ∧ deriv (hermite 2 1 0 0 0) 0 = 0 ∧ deriv (hermite 2 1 0 0 0) 2 = 0
    ∧ hermite 2 0 1 0 0 0 = 0 ∧ deriv (hermite 2 0 1 0 0) 0 = 1
    ∧ hermite 2 0 0 1 0 2 = 1 ∧ deriv (hermite 2 0 0 0 1) 2 = 1 := by
  refine ⟨(hermite_end_values (by norm_num) 1 0 0 0).1,
    (hermite_end_values (by norm_num) 1 0 0 0).2,
    (hermite_end_slopes (by norm_num) 1 0 0 0).1,
    (hermite_end_slopes (by norm_num) 1 0 0 0).2,
    (hermite_end_values (by norm_num) 0 1 0 0).1,
    (hermite_end_slopes (by norm_num) 0 1 0 0).1,
    (hermite_end_values (by norm_num) 0 0 1 0).2,
    (hermite_end_slopes (by norm_num) 0 0 0 1).2⟩

/-- Zero end data give the zero cubic, by uniqueness. -/
example (x : ℝ) : hermite 2 0 0 0 0 x = 0 := by
  have h := hermite_unique (L := 2) (by norm_num) 0 0 0 0 0 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x
  simpa using h.symm
