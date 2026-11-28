/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CapacityRepresentativesDefs
-- `List.mem_sections` reduces the representative choice to a finite search.
import Mathlib.Data.List.Sections

namespace MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Representative choices range over the sections of the list of sets. -/
private theorem feasible_iff (i : CapacityRepresentativesInstance) :
    CapacityRepresentativesFeasible i ↔ ∃ t ∈ i.1.sections,
      i.2.2 ≤ ∑ k ∈ Finset.range i.1.length, ∑ l ∈ (Finset.range i.1.length).filter (· ≠ k),
        capacity i (t.getD k 0) (t.getD l 0) := by
  simp only [CapacityRepresentativesFeasible, List.mem_sections]

/-- The capacity matrix over elements `0, 1, 2`: `c(1, 2) = 5` and `c(2, 1) = 1`. -/
private abbrev cap : List (List ℕ) := [[0, 0, 0], [0, 0, 5], [0, 1, 0]]

/-- Sets `{0, 1}` and `{2}` with bound `6`: representatives `1, 2` reach `5 + 1 = 6`. -/
private abbrev yes : CapacityRepresentativesInstance := ([[0, 1], [2]], cap, 6)

/-- The same sets with bound `7`: the best choice reaches only `6`. -/
private abbrev no : CapacityRepresentativesInstance := ([[0, 1], [2]], cap, 7)

/-- The decision problem accepts `yes`, with representatives `[1, 2]`. -/
example : capacityRepresentativesDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : CapacityRepresentativesFeasible yes := ⟨[1, 2], .cons (by decide) (.cons (by decide) .nil), by decide⟩
  simp [capacityRepresentativesDec, bitDecode_bitEncode, hw, hf]

/-- The other representative choice `[0, 2]` has capacity `0`. -/
example : ¬ yes.2.2 ≤ ∑ k ∈ Finset.range 2, ∑ l ∈ (Finset.range 2).filter (· ≠ k),
    capacity yes ([0, 2].getD k 0) ([0, 2].getD l 0) := by decide

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ capacityRepresentativesDec (bitEncode no) = false := by
  have hf : ¬ CapacityRepresentativesFeasible no := by rw [feasible_iff]; decide
  exact ⟨by unfold WellFormed; decide,
    by simp [capacityRepresentativesDec, bitDecode_bitEncode, hf]⟩

/-- Overlapping sets are malformed, although representatives `1, 2` still reach the bound. -/
example :
    CapacityRepresentativesFeasible (([[0, 1], [1, 2]], cap, 6) : CapacityRepresentativesInstance) ∧
      capacityRepresentativesDec
        (bitEncode (([[0, 1], [1, 2]], cap, 6) : CapacityRepresentativesInstance)) = false := by
  have hw : ¬ WellFormed (([[0, 1], [1, 2]], cap, 6) : CapacityRepresentativesInstance) := by
    unfold WellFormed; decide
  exact ⟨⟨[1, 2], .cons (by decide) (.cons (by decide) .nil), by decide⟩,
    by simp [capacityRepresentativesDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : capacityRepresentativesDec [true] = false := by
  have h : bitDecode (α := CapacityRepresentativesInstance) [true] = none := rfl
  simp [capacityRepresentativesDec, h]

end MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives
