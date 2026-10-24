/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Function.VanishingEndpointsDenseLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tests for density of endpoint-vanishing continuous functions in `L^p`

* The cutoff factor vanishes at the endpoints and equals `1` in the middle.
* The constant function `1` on `[0, 1]` is approximated in `L^2` by a
  continuous function vanishing at both endpoints.
* The identity function on `[0, 1]` is approximated in `L^1` by a continuous
  function vanishing at both endpoints.
* The zero function is approximated (its approximant has small `L^p` norm).
-/

open MeasureTheory
open scoped ENNReal
open MathlibExt.MeasureTheory.Function.VanishingEndpointsDenseLp

namespace MathlibExtTest.MeasureTheory.Function.VanishingEndpointsDenseLpTests

/-- The cutoff factor vanishes at the left endpoint. -/
example : vanishingCutoff 0 1 (1 / 4 : ℝ) 0 = 0 := by
  norm_num [vanishingCutoff]

/-- The cutoff factor vanishes at the right endpoint. -/
example : vanishingCutoff 0 1 (1 / 4 : ℝ) 1 = 0 := by
  norm_num [vanishingCutoff]

/-- The cutoff factor equals `1` in the middle of the interval. -/
example : vanishingCutoff 0 1 (1 / 4 : ℝ) (1 / 2 : ℝ) = 1 := by
  norm_num [vanishingCutoff]

/-- The constant function `1` on `[0, 1]` is approximated in `L^2` by a
continuous function vanishing at both endpoints. -/
example : ∃ g : ℝ → ℝ, Continuous g ∧ g 0 = 0 ∧ g 1 = 0 ∧
    MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
    eLpNorm ((fun _ : ℝ => (1 : ℝ)) - g) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1)) < 1 / 2 := by
  exact exists_continuous_vanishing_endpoints_eLpNorm_sub_lt 0 1 (by norm_num)
    (by norm_num) (by norm_num) (memLp_const 1) (by norm_num)

/-- The identity function on `[0, 1]` is approximated in `L^1` by a
continuous function vanishing at both endpoints. -/
example : ∃ g : ℝ → ℝ, Continuous g ∧ g 0 = 0 ∧ g 1 = 0 ∧
    MemLp g 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
    eLpNorm ((fun x : ℝ => x) - g) 1
      (volume.restrict (Set.Icc (0 : ℝ) 1)) < 1 / 4 := by
  have hmem : MemLp (fun x : ℝ => x) 1 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    refine MemLp.of_le (memLp_const (1 : ℝ)) continuous_id.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    show ‖x‖ ≤ ‖(1 : ℝ)‖
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1, norm_one]
    exact hx.2
  exact exists_continuous_vanishing_endpoints_eLpNorm_sub_lt 0 1 (by norm_num)
    le_rfl (by norm_num) hmem (by norm_num)

/-- The zero function has an endpoint-vanishing continuous approximant of
small `L^p` norm. -/
example : ∃ g : ℝ → ℝ, Continuous g ∧ g 0 = 0 ∧ g 1 = 0 ∧
    eLpNorm g 3 (volume.restrict (Set.Icc (0 : ℝ) 1)) < 1 / 2 := by
  obtain ⟨g, hgcont, hg0, hg1, -, hglt⟩ :=
    exists_continuous_vanishing_endpoints_eLpNorm_sub_lt (E := ℝ) (p := 3)
      (ε := (1 / 2 : ℝ≥0∞)) 0 1 (by norm_num) (by norm_num) (by norm_num)
      (f := fun _ => (0 : ℝ)) MemLp.zero (by norm_num)
  refine ⟨g, hgcont, hg0, hg1, ?_⟩
  have h : (fun _ : ℝ => (0 : ℝ)) - g = -g := by ext x; simp
  rwa [h, eLpNorm_neg] at hglt

end MathlibExtTest.MeasureTheory.Function.VanishingEndpointsDenseLpTests
