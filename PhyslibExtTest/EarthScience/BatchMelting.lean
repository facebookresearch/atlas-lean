/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.BatchMelting

/-!
# Batch melting checks

Concrete consumers of `PhyslibExt.EarthScience.BatchMelting`:
`C₀ = 10`, `F = 0.2`, `D = 0.1` (`Cl = 35.714…`, `Cs = 3.571…`), the
`F = 1` and `D = 1` boundaries, and total mass closure.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric batch melting
- B. Boundary cases

## iv. References

- `PhyslibExt.EarthScience.BatchMelting`
-/

/-- Numeric batch melting via the proved theorem, with mass closure. -/
example (Cl Cs : ℝ) (hcons : (10 : ℝ) = 0.2 * Cl + (1 - 0.2) * Cs)
    (hpart : Cs = 0.1 * Cl) :
    Cl = 10 / (0.1 + 0.2 * (1 - 0.1)) ∧ Cs = 0.1 * 10 / (0.1 + 0.2 * (1 - 0.1)) :=
  ⟨EarthScience.batch_melting_liquid (by norm_num) (by norm_num) (by norm_num) hcons hpart,
    EarthScience.batch_melting_solid (by norm_num) (by norm_num) (by norm_num) hcons hpart⟩

/-- Denominator positivity. -/
example : (0 : ℝ) < 0.1 + 0.2 * (1 - 0.1) :=
  EarthScience.batch_melting_denominator_pos (by norm_num) (by norm_num) (by norm_num)

/-- Boundary `F = 1`: `Cl = C₀`. -/
example (Cl Cs : ℝ) (hcons : (10 : ℝ) = 1 * Cl + (1 - 1) * Cs)
    (hpart : Cs = 0.1 * Cl) :
    Cl = 10 := by
  have h := EarthScience.batch_melting_liquid (D := 0.1) (F := 1) (C₀ := 10)
    (by norm_num) (by norm_num) (by norm_num) hcons hpart
  norm_num at h
  exact h

/-- Boundary `D = 1`: `Cl = C₀`. -/
example (Cl Cs : ℝ) (hcons : (10 : ℝ) = 0.2 * Cl + (1 - 0.2) * Cs)
    (hpart : Cs = 1 * Cl) :
    Cl = 10 := by
  have h := EarthScience.batch_melting_liquid (D := 1) (F := 0.2) (C₀ := 10)
    (by norm_num) (by norm_num) (by norm_num) hcons hpart
  norm_num at h
  exact h
