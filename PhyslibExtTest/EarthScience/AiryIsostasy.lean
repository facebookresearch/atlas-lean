/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.AiryIsostasy

/-!
# Airy isostasy checks

Concrete consumers of `PhyslibExt.EarthScience.AiryIsostasy`:
`ρc = 2700`, `ρm = 3300`, `h = 1000` (so the root is `4500`), the
zero-relief boundary, and a column outside the physical domain that only the
signed-algebra lemma covers.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric Airy column
- B. Zero-relief boundary
- C. Outside the physical domain

## iv. References

- `PhyslibExt.EarthScience.AiryIsostasy`
-/

/-- Numeric Airy root: `2700 * 1000 / (3300 - 2700) = 4500`. -/
example : (2700 : ℝ) * 1000 / (3300 - 2700) = 4500 := by norm_num

/-- Numeric Airy column: the root `4500` equalizes compensation pressure
for `T = 10000`, `D = 40000`. -/
example : (2700 : ℝ) * (10000 + 1000 + 4500) + 3300 * (40000 - 10000 - 4500)
    = 2700 * 10000 + 3300 * (40000 - 10000) := by norm_num

/-- Numeric Airy column via the signed-algebra lemma. -/
example : (2700 : ℝ) * (10000 + 1000 + 2700 * 1000 / (3300 - 2700))
      + 3300 * (40000 - 10000 - 2700 * 1000 / (3300 - 2700))
    = 2700 * 10000 + 3300 * (40000 - 10000) :=
  EarthScience.airy_root_pressure_eq_signed (by norm_num) (by norm_num)

/-- Numeric physical Airy column: `T = 10000`, `D = 40000` and root `4500`
satisfy the thickness hypotheses, the mantle below the root is `25500` thick,
and the pressures agree. -/
example : (0 : ℝ) ≤ 40000 - 10000 - 4500 ∧
    (2700 : ℝ) * (10000 + 1000 + 4500) + 3300 * (40000 - 10000 - 4500)
      = 2700 * 10000 + 3300 * (40000 - 10000) := by
  obtain ⟨-, -, hmantle, hpress⟩ :=
    EarthScience.airy_root_pressure_eq (ρc := 2700) (ρm := 3300) (h := 1000) (T := 10000)
      (D := 40000) (r := 4500) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact ⟨hmantle, hpress⟩

/-- Numeric converse: equal pressure at root `4500` forces the formula. -/
example : (4500 : ℝ) = 2700 * 1000 / (3300 - 2700) := by
  apply EarthScience.airy_root_of_pressure_eq_signed (ρc := 2700) (ρm := 3300) (h := 1000)
    (T := 10000) (D := 40000) (r := 4500) (by norm_num) (by norm_num)
  norm_num

/-- Numeric physical converse: the same column, with the thickness hypotheses. -/
example : (4500 : ℝ) = 2700 * 1000 / (3300 - 2700) :=
  (EarthScience.airy_root_of_pressure_eq (ρc := 2700) (ρm := 3300) (h := 1000) (T := 10000)
    (D := 40000) (r := 4500) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).1

/-- Zero relief: the Airy root is `0` when `h = 0`. -/
example : (2700 : ℝ) * 0 / (3300 - 2700) = 0 := by norm_num

/-- Zero relief via the proved nonnegativity theorem. -/
example : (0 : ℝ) ≤ (2700 : ℝ) * 0 / (3300 - 2700) :=
  (EarthScience.airy_root_nonneg_pos (by norm_num) (by norm_num) (by norm_num)).1

/-- Outside the physical domain: `ρc = 1`, `ρm = 2`, `h = 1`, `T = 10`,
`D = 5` gives root `1`, and the signed-algebra lemma still balances the
pressure expressions. -/
example : (1 : ℝ) * (10 + 1 + 1 * 1 / (2 - 1)) + 2 * (5 - 10 - 1 * 1 / (2 - 1))
    = 1 * 10 + 2 * (5 - 10) :=
  EarthScience.airy_root_pressure_eq_signed (by norm_num) (by norm_num)

/-- That elevated column has mantle thickness `D - T - r = -6`, so it fails the
compensation-depth hypothesis `T + r ≤ D` of `airy_root_pressure_eq`. -/
example : (5 : ℝ) - 10 - 1 * 1 / (2 - 1) = -6 ∧ ¬ ((10 : ℝ) + 1 * 1 / (2 - 1) ≤ 5) := by
  norm_num
