/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.WinklerFullContact

/-!
# Winkler full-contact checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.WinklerFullContact`:
at equality `a = |b| * B / 2` full contact holds with zero pressure
at one edge; below the threshold it fails.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Equality case: `a = 1`, `b = 1`, `B = 2` gives admission. -/
example : ∀ x ∈ Set.Icc (-2 / 2 : ℝ) (2 / 2),
    0 ≤ footingPressure 1 1 1 x :=
  (footingPressure_nonneg_iff (by norm_num) (by norm_num)).2
    (by norm_num)

/-- Below threshold: `a = 0`, `b = 1`, `B = 2` is not admissible. -/
example : ¬ ∀ x ∈ Set.Icc (-2 / 2 : ℝ) (2 / 2),
    0 ≤ footingPressure 1 0 1 x := by
  intro h
  have := h (-1) (by norm_num)
  norm_num [footingPressure] at this
