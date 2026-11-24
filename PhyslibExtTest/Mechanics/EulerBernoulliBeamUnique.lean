/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Mechanics.EulerBernoulliBeamUnique

/-!
# Quartic-uniqueness checks

Focused checks for
`PhyslibExt.Mechanics.EulerBernoulliBeamUnique`: at load
`w = 3`, rigidity `EI = 2`, span `L = 4`, the witness quartic
with coefficients `1 / 16, -1 / 2, 0, 4, 0` has midpoint value
`5`, through both the profile formula and the canonical
deflection.

These are elaboration and non-vacuity checks, not new results.
-/

open Mechanics.EulerBernoulli

/-- Midpoint value through the uniqueness conclusion. -/
example : quarticFun (1 / 16) (-1 / 2) 0 4 0 2 = 5 := by
  have h := quartic_unique (a := 1 / 16) (b := -1 / 2) (c := 0)
    (d := 4) (e := 0) (w := 3) (EI := 2) (L := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [quarticFun]) (by norm_num)
    (by norm_num [quarticFun]) (by norm_num) 2
  rw [h]
  norm_num

/-- The same witness against the canonical deflection. -/
example : quarticFun (1 / 16) (-1 / 2) 0 4 0 2
    = uniformLoadDeflection 3 2 4 2 :=
  quartic_unique_uniformLoadDeflection (a := 1 / 16) (b := -1 / 2)
    (c := 0) (d := 4) (e := 0) (w := 3) (EI := 2) (L := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [quarticFun]) (by norm_num)
    (by norm_num [quarticFun]) (by norm_num) 2
