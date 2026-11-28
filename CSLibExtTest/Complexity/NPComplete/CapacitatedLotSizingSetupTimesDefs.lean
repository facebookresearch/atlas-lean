/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimesDefs
-- `linarith` closes the real-valued capacity and demand inequalities.
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimes

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- One period and one item with unit processing time `1`, setup time `1` and demand `2`, and
capacity `3`. -/
private abbrev yes : CapacitatedLotSizingSetupTimesInstance := (1, [(1, 1, [2])], [3])

/-- The same item with capacity `2`: producing the demand `2` also needs the setup time `1`. -/
private abbrev no : CapacitatedLotSizingSetupTimesInstance := (1, [(1, 1, [2])], [2])

/-- The decision problem accepts `yes`: produce `2` units with the setup on, using `2 + 1 = 3`
units of capacity. -/
example : capacitatedLotSizingSetupTimesDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : CapacitatedLotSizingSetupTimesFeasible yes := by
    refine ⟨fun _ _ => 2, fun _ _ => true, fun _ _ => by norm_num, fun _ _ _ => rfl, ?_, ?_⟩
    · intro j t
      obtain rfl : j = ⟨0, by decide⟩ :=
        Fin.ext (by have : (j : ℕ) < 1 := j.2; show (j : ℕ) = 0; omega)
      obtain rfl : t = 0 := Subsingleton.elim _ _
      simp
    · intro t
      obtain rfl : t = 0 := Subsingleton.elim _ _
      simp
      norm_num
  simp [capacitatedLotSizingSetupTimesDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ capacitatedLotSizingSetupTimesDec (bitEncode no) = false := by
  have hf : ¬ CapacitatedLotSizingSetupTimesFeasible no := by
    rintro ⟨x, y, -, hy, hd, hc⟩
    have hd0 := hd 0 0
    have hc0 := hc 0
    simp at hd0 hc0
    rw [hy 0 0 (by linarith)] at hc0
    simp at hc0
    linarith
  exact ⟨by unfold WellFormed; decide,
    by simp [capacitatedLotSizingSetupTimesDec, bitDecode_bitEncode, hf]⟩

/-- An item with two demands in a one-period instance is malformed, although producing nothing
meets its only counted demand `0`. -/
example :
    CapacitatedLotSizingSetupTimesFeasible
        ((1, [(1, 0, [0, 5])], [3]) : CapacitatedLotSizingSetupTimesInstance) ∧
      capacitatedLotSizingSetupTimesDec
        (bitEncode ((1, [(1, 0, [0, 5])], [3]) : CapacitatedLotSizingSetupTimesInstance)) =
          false := by
  have hw : ¬ WellFormed ((1, [(1, 0, [0, 5])], [3]) : CapacitatedLotSizingSetupTimesInstance) := by
    unfold WellFormed; decide
  refine ⟨⟨fun _ _ => 0, fun _ _ => false, fun _ _ => le_rfl, fun _ _ h => absurd h (lt_irrefl _),
    ?_, ?_⟩, by simp [capacitatedLotSizingSetupTimesDec, bitDecode_bitEncode, hw]⟩
  · intro j t
    obtain rfl : j = ⟨0, by decide⟩ :=
      Fin.ext (by have : (j : ℕ) < 1 := j.2; show (j : ℕ) = 0; omega)
    obtain rfl : t = 0 := Subsingleton.elim _ _
    simp
  · intro t
    obtain rfl : t = 0 := Subsingleton.elim _ _
    simp

/-- A lone continuation bit is a truncated instance encoding. -/
example : capacitatedLotSizingSetupTimesDec [true] = false := by
  have h : bitDecode (α := CapacitatedLotSizingSetupTimesInstance) [true] = none := rfl
  simp [capacitatedLotSizingSetupTimesDec, h]

end MetaMathlibExt.Complexity.NPComplete.CapacitatedLotSizingSetupTimes
