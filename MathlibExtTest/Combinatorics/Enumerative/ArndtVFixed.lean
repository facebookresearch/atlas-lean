/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ArndtVFixed

/-! # Tests for the compositions fixed by V -/

open MetaMathlibExt

example (c : Composition 0) : arndtV c.blocks = c.blocks := by
  apply (arndtV_fixed_iff_and_count.1 0 c).mpr
  simp [(c.blocks_eq_nil).mpr rfl]

-- The third part must be one, even when the first pair is fixed.
example (c : Composition 7) (hc : c.blocks = [1, 3, 3]) : arndtV c.blocks ≠ c.blocks := by
  intro h
  have hthird := (arndtV_fixed_iff_and_count.1 7 c).mp h 2 (by simp [hc])
  simp [hc] at hthird

-- At weights eight and nine, both branches of the recurrence contribute.
example :
    (Finset.univ.filter fun c : Composition 8 => arndtV c.blocks = c.blocks).card = 2 ∧
    (Finset.univ.filter fun c : Composition 9 => arndtV c.blocks = c.blocks).card = 2 := by
  obtain ⟨_, _, _, _, _, _, hfib⟩ := arndtV_fixed_iff_and_count
  exact hfib 4 (by decide)
