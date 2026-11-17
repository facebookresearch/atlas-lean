/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.CombustionAcoustics

/-!
# Arrhenius equilibrium checks

Concrete consumers of `PhyslibExt.Chemistry.CombustionAcoustics`:
unit-rate parameters `G = H = B = Ta = 1`, whose equilibrium lies in
`(1, 2)` with zero rate, and the constant solution at an equilibrium
is trapped.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-parameter equilibrium

## iv. References

- `PhyslibExt.Chemistry.CombustionAcoustics`
-/

/-- An equilibrium in `(1, 2)` for the unit parameters. -/
example : ∃ T : ℝ, T ∈ Set.Ioo 1 (1 + 1 / 1) ∧
    CombustionAcoustics.arrheniusRate 1 1 1 1 T = 0 :=
  CombustionAcoustics.arrhenius_equilibrium_exists (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The rate at ambient `1` is `exp (-1)`, positive. -/
example : CombustionAcoustics.arrheniusRate 1 1 1 1 1 = Real.exp (-1) ∧
    0 < CombustionAcoustics.arrheniusRate 1 1 1 1 1 :=
  ⟨by simpa using CombustionAcoustics.arrheniusRate_ambient 1 1 1 1,
   CombustionAcoustics.arrheniusRate_pos_ambient (by norm_num)⟩
