/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.EntireZerosOnesLines

/-! # Tests for entire functions with zeros and one-points on lines -/

open MathlibExt.Analysis.EntireZerosOnesLinesWanted

-- The direction vector in a line ensures that its points at parameters zero and one differ.
example : ¬ IsComplexLine ({0} : Set ℂ) := by
  rintro ⟨a, v, hv, h⟩
  have hmem (t : ℝ) : a + t • v ∈ ({0} : Set ℂ) := by
    rw [h]
    exact ⟨t, rfl⟩
  have ha : a = 0 := by simpa using hmem 0
  exact hv (by simpa [ha] using hmem 1)

-- The exponential omits zero and takes the value one at the origin.
example : ZerosOnLine Complex.exp ∅ ∧ ¬ OnesOnLine Complex.exp ∅ :=
  ⟨fun z hz ↦ (Complex.exp_ne_zero z hz).elim, fun h ↦ h 0 Complex.exp_zero⟩
