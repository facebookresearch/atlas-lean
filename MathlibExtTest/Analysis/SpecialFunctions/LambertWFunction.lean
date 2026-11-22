/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction

namespace MetaMathlibExt

example : lambertMap 0 = 0 := by
  simp [lambertMap]

example : lambertMap (-1) = -Real.exp (-1) := by
  simp [lambertMap]

example : ∃! y : { y : ℝ // -1 < y }, lambertMap y.val = 0 := by
  apply existsUnique_lambertMap_preimage 0
  have h := Real.exp_pos (-1)
  linarith

example (y : { y : ℝ // -1 < y }) (hy : lambertMap y.val = 0) : y.val = 0 := by
  have hx : -Real.exp (-1) < (0 : ℝ) := by
    have h := Real.exp_pos (-1)
    linarith
  have hU := existsUnique_lambertMap_preimage 0 hx
  have h0 : lambertMap (⟨0, by norm_num⟩ : { y : ℝ // -1 < y }).val = 0 := by
    simp [lambertMap]
  have heq := hU.unique hy h0
  exact congrArg Subtype.val heq

example : ∃ y ≤ (-1 : ℝ), lambertMap y = -Real.exp (-1) / 2 := by
  have he := Real.exp_pos (-1)
  obtain ⟨y, hy⟩ := (existsUnique_lambertMap_lower_preimage
    (x := -Real.exp (-1) / 2) (by linarith) (by linarith)).exists
  exact ⟨y.val, y.property, hy⟩

example (y : { y : ℝ // y ≤ -1 }) (hy : lambertMap y.val = -Real.exp (-1)) :
    y.val = -1 := by
  have he := Real.exp_pos (-1)
  have hU := existsUnique_lambertMap_lower_preimage (x := -Real.exp (-1)) le_rfl (by linarith)
  have h0 : lambertMap (⟨-1, le_rfl⟩ : { y : ℝ // y ≤ -1 }).val = -Real.exp (-1) := by
    simp [lambertMap]
  exact congrArg Subtype.val (hU.unique hy h0)

end MetaMathlibExt
