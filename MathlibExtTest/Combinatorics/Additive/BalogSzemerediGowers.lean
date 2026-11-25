/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.BalogSzemerediGowers
import Mathlib.Tactic.NormNum

open scoped Pointwise
open MathlibExt.Combinatorics.Additive.FreimanBSGWanted

-- For the empty set the energy hypothesis holds even for density greater than one.
example (n : ℕ) : ∃ U ⊆ (∅ : Finset (Fin n → ℤ)), ((U - U).card : ℝ) ≤ 0 := by
  obtain ⟨U, hU, _, hdiff⟩ := balog_szemeredi_gowers n ∅ 2 (by norm_num) (by simp)
  exact ⟨U, hU, by simpa using hdiff⟩

-- The pair {0, 1} has energy six, so the lower bound at density 3/4 forces a nonempty witness.
example : ∃ U ⊆ ({0, 1} : Finset (Fin 1 → ℤ)), U.Nonempty ∧
    ((U - U).card : ℝ) ≤ 2 ^ 38 * (4 / 3 : ℝ) ^ 24 * 2 := by
  let A : Finset (Fin 1 → ℤ) := {0, 1}
  have hcard : A.card = 2 := by decide
  have henergy : A.addEnergy A = 6 := by decide
  obtain ⟨U, hU, hsize, hdiff⟩ := balog_szemeredi_gowers 1 A (3 / 4) (by norm_num) (by
    rw [hcard, henergy]; norm_num)
  refine ⟨U, hU, Finset.card_pos.mp ?_, ?_⟩
  · rw [hcard] at hsize
    have hpos : (0 : ℝ) < U.card := lt_of_lt_of_le (by norm_num) hsize
    exact_mod_cast hpos
  · simpa only [hcard, Nat.cast_ofNat, inv_div] using hdiff
