/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MaximumNimGrundyPPositions

/-! # Tests for `MathlibExt.Combinatorics.MaximumNimGrundyPPositions` -/

namespace MathlibExtTest.MaximumNimGrundyPPositions

open MetaMathlibExt

private theorem half_rule (m : ℕ) (_hm : 1 ≤ m) :
    (m - 1) / 2 ≤ m / 2 ∧ m / 2 ≤ (m - 1) / 2 + 1 := by omega

-- A positive P-position for the halving rule.
example : SpragueGrundy.IsP (maximumNimGame (· / 2)) (3 : ℕ) :=
  (maximumNimGrundy_eq_zero_iff_isP (· / 2) rfl half_rule 3).mp
    maximumNimGrundy_div_two_three

-- The next pile is not a P-position: its Grundy value is two.
example : ¬SpragueGrundy.IsP (maximumNimGame (· / 2)) (4 : ℕ) := by
  intro hp
  have hz := (maximumNimGrundy_eq_zero_iff_isP (· / 2) rfl half_rule 4).mpr hp
  rw [maximumNimGrundy_div_two_four] at hz
  contradiction

-- The empty pile is terminal, including for the rule that allows any positive removal.
example : SpragueGrundy.IsP (maximumNimGame (fun x => x)) (0 : ℕ) := by
  apply (maximumNimGrundy_eq_zero_iff_isP (fun x => x) rfl (fun m hm => by omega) 0).mp
  rw [maximumNimGrundy_eq, maximumNimMex_eq_iff]
  simp

end MathlibExtTest.MaximumNimGrundyPPositions
