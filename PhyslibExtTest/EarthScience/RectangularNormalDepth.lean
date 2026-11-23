/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.RectangularNormalDepth

/-!
# Rectangular normal-depth checks

Focused checks for
`PhyslibExt.EarthScience.RectangularNormalDepth`: at unit
prefactor and width `4`, depth `2` discharges more than depth
`1`, and equal discharges at positive depths force equal depths.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Strict increase at two concrete depths. -/
example : rectangularDischarge 1 4 1 < rectangularDischarge 1 4 2 :=
  rectangularDischarge_strictMonoOn (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- Uniqueness applied at a concrete pair. -/
example {h : ℝ} (hh : 0 < h)
    (heq : rectangularDischarge 1 4 h = rectangularDischarge 1 4 2) :
    h = 2 :=
  rectangular_normal_depth_unique (by norm_num) (by norm_num) hh
    (by norm_num) heq
