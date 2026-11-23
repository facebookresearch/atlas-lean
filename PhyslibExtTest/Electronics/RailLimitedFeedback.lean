/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.RailLimitedFeedback
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.RailLimitedFeedback

namespace PhyslibExtTest.Electronics.RailLimitedFeedback

/-- Existence and uniqueness at concrete values: gain `9`, unit
feedback, rails `[-5, 5]`, unit input. -/
example : ∃! vo : ℝ, vo = railLimitedMap 9 1 (-5) 5 1 vo :=
  existsUnique_fixedPoint 9 1 (-5) 5 1 (by norm_num) (by norm_num) (by norm_num)

/-- In the linear regime the fixed point is the linear candidate
`9 * 1 / (1 + 9 * 1) = 9/10`, which lies inside the rails. -/
example (vo : ℝ) (h : vo = railLimitedMap 9 1 (-5) 5 1 vo) : vo = 9 / 10 := by
  have hcand : linearCandidate 9 1 1 ∈ Set.Icc (-5 : ℝ) 5 := by
    norm_num [linearCandidate]
  have h2 := eq_linearCandidate_of_mem 9 1 (-5) 5 1 vo (by norm_num) (by norm_num)
    (by norm_num) h hcand
  rw [h2]
  norm_num [linearCandidate]

/-- Direct check: `9/10` really is a fixed point at those values. -/
example : (9 / 10 : ℝ) = railLimitedMap 9 1 (-5) 5 1 (9 / 10) := by
  norm_num [railLimitedMap, railClamp, linearCandidate]

/-- Saturated regime: input `100` gives linear candidate `90`, above
the upper rail, so the unique fixed point is the rail `5`. -/
example : (5 : ℝ) = railLimitedMap 9 1 (-5) 5 100 5 := by
  norm_num [railLimitedMap, railClamp]

example (vo : ℝ) (h : vo = railLimitedMap 9 1 (-5) 5 100 vo) : vo = 5 :=
  fixedPoint_unique 9 1 (-5) 5 100 (by norm_num) (by norm_num) (by norm_num)
    vo 5 h (by norm_num [railLimitedMap, railClamp])

/-- The clamp itself at and beyond the closed endpoints. -/
example : railClamp (-5 : ℝ) 5 7 = 5 := by norm_num [railClamp]
example : railClamp (-5 : ℝ) 5 (-7) = -5 := by norm_num [railClamp]
example : railClamp (-5 : ℝ) 5 5 = 5 := by norm_num [railClamp]
example : railClamp (-5 : ℝ) 5 (-5) = -5 := by norm_num [railClamp]

/-- Zero input: the candidate is `0`, inside the rails, and it is the
fixed point. -/
example (vo : ℝ) (h : vo = railLimitedMap 9 1 (-5) 5 0 vo) : vo = 0 := by
  have hcand : linearCandidate 9 1 0 ∈ Set.Icc (-5 : ℝ) 5 := by
    norm_num [linearCandidate]
  have h2 := eq_linearCandidate_of_mem 9 1 (-5) 5 0 vo (by norm_num) (by norm_num)
    (by norm_num) h hcand
  rw [h2]
  norm_num [linearCandidate]

end PhyslibExtTest.Electronics.RailLimitedFeedback
