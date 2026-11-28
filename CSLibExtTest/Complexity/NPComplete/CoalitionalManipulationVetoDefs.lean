/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CoalitionalManipulationVetoDefs
-- `List.mem_permutations'` reduces a manipulative vote to a finite search.
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationVeto

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open CoalitionalManipulationBorda

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

/-- One nonmanipulative vote `1 2 0` (vetoing `0`) and two manipulators of weight `2`. -/
private abbrev yes : CoalitionalManipulationInstance := ([([1, 2, 0], 1)], [2, 2], 0)

/-- The same vote and a single manipulator of weight `2`, who can veto only one rival. -/
private abbrev no : CoalitionalManipulationInstance := ([([1, 2, 0], 1)], [2], 0)

/-- The decision problem accepts `yes`: the manipulators veto `1` and `2` respectively, giving
scores `4, 3, 3`. -/
example : coalitionalManipulationVetoDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed IsRanking; decide
  have hf : CoalitionalManipulationVetoFeasible yes :=
    ⟨[[0, 2, 1], [0, 1, 2]], rfl, by unfold IsRanking; decide, by decide⟩
  simp [coalitionalManipulationVetoDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ coalitionalManipulationVetoDec (bitEncode no) = false := by
  have hf : ¬ CoalitionalManipulationVetoFeasible no := by
    unfold CoalitionalManipulationVetoFeasible
    rw [feasible_one_iff]
    decide
  exact ⟨by unfold WellFormed IsRanking; decide,
    by simp [coalitionalManipulationVetoDec, bitDecode_bitEncode, hf]⟩

/-- The scoring vector matters: under Borda the single weight-`2` manipulator of `no` succeeds
with the vote `0 2 1`. -/
example : CoalitionalManipulationBordaFeasible no :=
  ⟨[[0, 2, 1]], rfl, by unfold IsRanking; decide, by decide⟩

/-- The vote `0 0` is not a ranking, so the instance is malformed, although `0` already wins
under the scoring of that list. -/
example :
    CoalitionalManipulationVetoFeasible (([([0, 0], 1)], [], 0) : CoalitionalManipulationInstance) ∧
      coalitionalManipulationVetoDec
        (bitEncode (([([0, 0], 1)], [], 0) : CoalitionalManipulationInstance)) = false := by
  have hw : ¬ WellFormed (([([0, 0], 1)], [], 0) : CoalitionalManipulationInstance) := by
    unfold WellFormed IsRanking; decide
  exact ⟨⟨[], rfl, by simp, by decide⟩,
    by simp [coalitionalManipulationVetoDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : coalitionalManipulationVetoDec [true] = false := by
  have h : bitDecode (α := CoalitionalManipulationInstance) [true] = none := rfl
  simp [coalitionalManipulationVetoDec, h]

end MetaMathlibExt.Complexity.NPComplete.CoalitionalManipulationVeto
