/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ParentDaughterConservation

import Mathlib.Tactic.NormNum

/-!
# Parent/daughter branch conservation checks

Concrete consumers of `PhyslibExt.EarthScience.ParentDaughterConservation`:
a generic elaboration check, the single-branch case `f = 1` where the
plain total `P + D` is conserved, and the no-initial-daughter case
`D0 = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
exponential keeps the checks symbolic: the numeric content is the
algebra of the branch-weighted total.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ParentDaughterConservation`
-/

/-- Generic elaboration: the theorem applies to any decay constant,
initial inventories, nonzero branch fraction, and time. -/
example {lam P0 D0 f t : ℝ} (hf : f ≠ 0) :
    (P0 * Real.exp (-lam * t))
      + (D0 + f * (P0 - P0 * Real.exp (-lam * t))) / f
      = P0 + D0 / f :=
  EarthScience.parent_daughter_branch_conservation hf

/-- Single branch `f = 1`: the plain total `P(t) + D(t)` equals
`P0 + D0`. -/
example {lam P0 D0 t : ℝ} :
    (P0 * Real.exp (-lam * t))
      + (D0 + 1 * (P0 - P0 * Real.exp (-lam * t)))
      = P0 + D0 := by
  have h := EarthScience.parent_daughter_branch_conservation
    (lam := lam) (P0 := P0) (D0 := D0) (f := (1 : ℝ)) (t := t) (by norm_num)
  simp_all

/-- No initial daughter `D0 = 0`, branch fraction `f = 2/5`: the
branch-weighted total is `P0`. -/
example {lam P0 t : ℝ} :
    (P0 * Real.exp (-lam * t))
      + (0 + (2 / 5 : ℝ) * (P0 - P0 * Real.exp (-lam * t))) / (2 / 5 : ℝ)
      = P0 := by
  have h := EarthScience.parent_daughter_branch_conservation
    (lam := lam) (P0 := P0) (D0 := (0 : ℝ)) (f := (2 / 5 : ℝ)) (t := t) (by norm_num)
  simp_all
