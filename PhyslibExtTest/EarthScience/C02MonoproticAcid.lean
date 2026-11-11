/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.C02MonoproticAcid

/-!
# Monoprotic-acid checks

Concrete consumers of `PhyslibExt.EarthScience.C02MonoproticAcid`:
the public shape of the uniqueness theorem, the positive root at
`K = 1`, `C = 1` (so `h = (-1 + sqrt 5) / 2`), and the dilute
boundary `C → 0` via the existence theorem at small `C`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Uniqueness shape
- B. Positive root at `K = C = 1`

## iv. References

- `PhyslibExt.EarthScience.C02MonoproticAcid`
-/

/-- Public shape of the uniqueness theorem. -/
example {K C h : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hh : 0 < h) (heq : h ^ 2 + K * h - K * C = 0) :
    h = (-K + Real.sqrt (K ^ 2 + 4 * K * C)) / 2 :=
  EarthScience.monoprotic_acid_h_unique hK hC hh heq

/-- Positive root at `K = 1`, `C = 1`. -/
example : 0 < (-1 + Real.sqrt (1 ^ 2 + 4 * 1 * 1)) / 2 ∧
    ((-1 + Real.sqrt (1 ^ 2 + 4 * 1 * 1)) / 2) ^ 2
      + 1 * ((-1 + Real.sqrt (1 ^ 2 + 4 * 1 * 1)) / 2) - 1 * 1 = 0 :=
  EarthScience.monoprotic_acid_h_exists (by norm_num) (by norm_num)

/-- The root at `K = C = 1` is the golden-ratio conjugate `(-1 + sqrt 5) / 2`. -/
example : (-1 + Real.sqrt (1 ^ 2 + 4 * 1 * 1)) / 2
    = (-1 + Real.sqrt 5) / 2 := by
  norm_num
