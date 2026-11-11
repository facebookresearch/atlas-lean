/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.C03HenryLaw

/-!
# Henry's-law checks

Concrete consumers of `PhyslibExt.EarthScience.C03HenryLaw`:
`H = 0.034`, `p = 1` (so `c = 0.034`, doubled `0.068`), the zero-pressure
boundary, and the reciprocal conversion with `H_pc = 2`, `H_cp = 1 / 2`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Doubling and zero pressure
- B. Convention conversion

## iv. References

- `PhyslibExt.EarthScience.C03HenryLaw`
-/

/-- Doubling, numeric: `0.034 * (2 * 1) = 2 * 0.034`. -/
example : (0.034 : ℝ) * (2 * 1) = 2 * 0.034 :=
  EarthScience.henry_doubling (by norm_num)

/-- Zero-pressure boundary: `0.034 * 0 = 0`. -/
example : (0.034 : ℝ) * (0 : ℝ) = 0 :=
  EarthScience.henry_zero_pressure

/-- Reciprocal conversion, numeric: `H_pc = 2` gives `H_cp = 1 / 2` and back. -/
example : (2 : ℝ) = 1 / (1 / 2) :=
  EarthScience.henry_conversion_reciprocal (by norm_num) (by norm_num)

/-- Public shape of the doubling theorem. -/
example {H p c : ℝ} (h : c = H * p) : H * (2 * p) = 2 * c :=
  EarthScience.henry_doubling h
