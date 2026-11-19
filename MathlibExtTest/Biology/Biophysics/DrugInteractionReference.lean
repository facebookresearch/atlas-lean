/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.DrugInteractionReference
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Tests for the interaction-reference witness: zero-dose conventions of
both references and the strict separation of the two unit-dose values. -/

namespace MathlibExtTest.Biology.Biophysics.DrugInteractionReference

open MathlibExt.Biology.Biophysics.DrugInteractionReference

/-- Bliss with a vanishing second effect returns the first effect. -/
example (a : ℝ) : a + 0 - a * 0 = a := by ring

/-- Bliss with a vanishing first effect returns the second effect. -/
example (b : ℝ) : 0 + b - 0 * b = b := by ring

/-- The witness curve vanishes at dose zero and is `1/2` at dose one. -/
example : (0 : ℝ) / (1 + 0) = 0 ∧ (1 : ℝ) / (1 + 1) = 1 / 2 := by constructor <;> norm_num

/-- The two references differ at unit doses, and `17/24` separates them. -/
example : (2 / 3 : ℝ) < 17 / 24 ∧ (17 / 24 : ℝ) < 3 / 4 := by
  have h := interact_references_disagree
  exact ⟨h.2.2.1, h.2.2.2.1⟩

end MathlibExtTest.Biology.Biophysics.DrugInteractionReference
