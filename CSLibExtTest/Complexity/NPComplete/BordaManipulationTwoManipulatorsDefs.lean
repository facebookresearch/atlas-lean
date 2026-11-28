/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BordaManipulationTwoManipulatorsDefs
-- `List.mem_permutations'` reduces the manipulative votes to a finite search.
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- The manipulative votes range over the permutations of the candidates. -/
private theorem feasible_iff (i : BordaManipulationInstance) :
    BordaManipulationFeasible i ↔ ∃ w₁ ∈ (List.range i.1).permutations',
      ∃ w₂ ∈ (List.range i.1).permutations', ∀ d < i.1,
        bordaScore i.1 (i.2.1 ++ [w₁, w₂]) d ≤ bordaScore i.1 (i.2.1 ++ [w₁, w₂]) i.2.2 := by
  simp only [BordaManipulationFeasible, IsVote, List.mem_permutations', exists_and_left]

/-- One vote `1 2 0`; two manipulators can lift `0` to the top. -/
private abbrev yes : BordaManipulationInstance := (3, [[1, 2, 0]], 0)

/-- Votes `1 2 0`, `1 2 0`, `1 0 2` give `1` six points and `0` one; two manipulators add at
most four to `0`. -/
private abbrev no : BordaManipulationInstance := (3, [[1, 2, 0], [1, 2, 0], [1, 0, 2]], 0)

/-- The decision problem accepts `yes`, with manipulative votes `0 2 1` and `0 1 2`
(scores `4, 3, 2`). -/
example : bordaManipulationDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed IsVote; decide
  have hf : BordaManipulationFeasible yes := ⟨[0, 2, 1], [0, 1, 2], by unfold IsVote; decide, by unfold IsVote; decide, by decide⟩
  simp [bordaManipulationDec, bitDecode_bitEncode, hw, hf]

/-- The manipulation is not automatic: the votes `1 0 2` and `2 0 1` leave `0` with `2` points
against `4` for `1`. -/
example : ¬ ∀ d < 3, bordaScore 3 ([[1, 2, 0]] ++ [[1, 0, 2], [2, 0, 1]]) d ≤
    bordaScore 3 ([[1, 2, 0]] ++ [[1, 0, 2], [2, 0, 1]]) 0 := by
  decide

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ bordaManipulationDec (bitEncode no) = false := by
  have hf : ¬ BordaManipulationFeasible no := by rw [feasible_iff]; decide
  exact ⟨by unfold WellFormed IsVote; decide, by simp [bordaManipulationDec, bitDecode_bitEncode, hf]⟩

/-- The vote `[0]` is not a ranking of the three candidates, so the instance is malformed,
although the manipulative votes `0 1 2` and `0 2 1` make `0` win under the scoring of that list. -/
example :
    BordaManipulationFeasible ((3, [[0]], 0) : BordaManipulationInstance) ∧
      bordaManipulationDec (bitEncode ((3, [[0]], 0) : BordaManipulationInstance)) = false := by
  have hw : ¬ WellFormed ((3, [[0]], 0) : BordaManipulationInstance) := by
    unfold WellFormed IsVote; decide
  exact ⟨⟨[0, 1, 2], [0, 2, 1], by unfold IsVote; decide, by unfold IsVote; decide, by decide⟩,
    by simp [bordaManipulationDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : bordaManipulationDec [true] = false := by
  have h : bitDecode (α := BordaManipulationInstance) [true] = none := rfl
  simp [bordaManipulationDec, h]

end MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators
