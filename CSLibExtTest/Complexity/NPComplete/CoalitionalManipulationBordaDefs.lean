/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CoalitionalManipulationBordaDefs
-- `List.mem_permutations'` reduces a manipulative vote to a finite search.
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- With one manipulator its vote ranges over the permutations of the candidates. -/
private theorem feasible_one_iff (α : List ℕ) (S : List (List ℕ × ℕ)) (w p : ℕ) :
    ManipulationFeasible α (S, [w], p) ↔ ∃ v ∈ [0, 1, 2].permutations',
      ∀ c < 3, c ≠ p → score α (S ++ [(v, w)]) c < score α (S ++ [(v, w)]) p := by
  constructor
  · rintro ⟨T, hT, hr, h⟩
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.1 hT
    exact ⟨v, List.mem_permutations'.2 (hr v (by simp)), h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨[v], rfl, by simpa [IsRanking] using List.mem_permutations'.1 hv, h⟩

/-- One nonmanipulative vote `1 2 0` and one manipulator of weight `2`. -/
private abbrev yes : CoalitionalManipulationInstance := ([([1, 2, 0], 1)], [2], 0)

/-- The same vote and one manipulator of weight `1`: at best all three candidates tie at `2`. -/
private abbrev no : CoalitionalManipulationInstance := ([([1, 2, 0], 1)], [1], 0)

/-- The decision problem accepts `yes`: the manipulator votes `0 2 1`, giving scores
`4, 2, 3`. -/
example : coalitionalManipulationBordaDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed IsRanking; decide
  have hf : CoalitionalManipulationBordaFeasible yes :=
    ⟨[[0, 2, 1]], rfl, by unfold IsRanking; decide, by decide⟩
  simp [coalitionalManipulationBordaDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`: the manipulator's weight
matters. -/
example : WellFormed no ∧ coalitionalManipulationBordaDec (bitEncode no) = false := by
  have hf : ¬ CoalitionalManipulationBordaFeasible no := by
    unfold CoalitionalManipulationBordaFeasible
    rw [feasible_one_iff]
    decide
  exact ⟨by unfold WellFormed IsRanking; decide,
    by simp [coalitionalManipulationBordaDec, bitDecode_bitEncode, hf]⟩

/-- The vote `0 0` is not a ranking, so the instance is malformed, although `0` already wins
under the scoring of that list. -/
example :
    CoalitionalManipulationBordaFeasible (([([0, 0], 1)], [], 0) : CoalitionalManipulationInstance) ∧
      coalitionalManipulationBordaDec
        (bitEncode (([([0, 0], 1)], [], 0) : CoalitionalManipulationInstance)) = false := by
  have hw : ¬ WellFormed (([([0, 0], 1)], [], 0) : CoalitionalManipulationInstance) := by
    unfold WellFormed IsRanking; decide
  exact ⟨⟨[], rfl, by simp, by decide⟩,
    by simp [coalitionalManipulationBordaDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : coalitionalManipulationBordaDec [true] = false := by
  have h : bitDecode (α := CoalitionalManipulationInstance) [true] = none := rfl
  simp [coalitionalManipulationBordaDec, h]

end MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationBorda
