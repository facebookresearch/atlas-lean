/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosinePowerAreaRecurrence
import Mathlib.Tactic.NormNum

/-! # Tests for the recursion of limiting cosine-power areas -/

namespace MathlibExtTest.CosinePowerAreaRecurrence

open Real Filter Topology MetaMathlibExt

-- The first odd case uses the limit at exponent one and the odd correction.
example : ∃ L L' : ℝ, Tendsto (cosPowArea 3) atTop (𝓝 L) ∧
    Tendsto (cosPowArea 1) atTop (𝓝 L') ∧ L = 2 / 3 * L' + 8 / (9 * π) := by
  obtain ⟨L, L', h₃, h₁, h⟩ := cosPowArea_limit_recursion (n := 3) (by decide)
  refine ⟨L, L', h₃, h₁, ?_⟩
  norm_num [Nat.odd_iff] at h ⊢
  exact h

-- The first even case uses the limit at exponent two and the even correction.
example : ∃ L L' : ℝ, Tendsto (cosPowArea 4) atTop (𝓝 L) ∧
    Tendsto (cosPowArea 2) atTop (𝓝 L') ∧ L = 3 / 4 * L' + 16 / (16 * π) := by
  obtain ⟨L, L', h₄, h₂, h⟩ := cosPowArea_limit_recursion (n := 4) (by decide)
  refine ⟨L, L', h₄, h₂, ?_⟩
  norm_num [Nat.odd_iff] at h ⊢
  exact h

/-- info: 'MetaMathlibExt.cosPowArea_limit_recursion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MetaMathlibExt.cosPowArea_limit_recursion

end MathlibExtTest.CosinePowerAreaRecurrence
