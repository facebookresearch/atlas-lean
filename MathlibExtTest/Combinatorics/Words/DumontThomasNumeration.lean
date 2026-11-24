/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Combinatorics.Words.DumontThomasNumeration

namespace MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail

private def letterMap : Bool → List Bool
  | false => [true, false]
  | true => [false, false]

private def path : ℕ → List Bool × Bool
  | 0 => ([], true)
  | _ + 1 => ([true], false)

private theorem letterMap_isSubstitution : IsSubstitution letterMap := by
  refine ⟨fun a => by cases a <;> decide, false, Filter.tendsto_atTop_atTop.mpr ?_⟩
  intro n
  refine ⟨n, fun k hk => ?_⟩
  have hlen (a : Bool) : (letterMap a).length = 2 := by cases a <;> rfl
  simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le

-- The first digit skips a block of length two. Reversing the digits selects a different letter.
example : (morphIterate letterMap 2 [false])[2]? =
    substitutionAutomaton letterMap false [1, 0] := by
  have hadm : IsLetterAdmissibleSequence letterMap false path 1 := by
    refine ⟨fun i hi => ?_, ⟨[], rfl⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[false], rfl⟩
  exact morphIterate_getElem_eq_substitutionAutomaton_tail
    letterMap letterMap_isSubstitution 2 (by decide) false path hadm

-- At depth zero the terminal word is unchanged and the only summand is `|m₀|`.
example : (∑ j ∈ Finset.range (0 + 1), (morphIterate letterMap j [true]).length) <
    (morphIterate letterMap 0 [true, false]).length :=
  admissibleSequence_weightedLength_lt letterMap letterMap_isSubstitution
    (fun _ => ([true], false)) 0 (isAdmissibleSequence_zero _ _)

-- Two transitions: `m₁a₁` is a full image, while `m₀a₀` is a proper prefix.
example : (∑ j ∈ Finset.range (2 + 1), (morphIterate letterMap j (path j).1).length) <
    (morphIterate letterMap 2 [true, false]).length := by
  apply admissibleSequence_weightedLength_lt letterMap letterMap_isSubstitution path 2
  intro i hi
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact ⟨[false], rfl⟩
  · exact ⟨[], rfl⟩

example : substitutionAutomaton letterMap false [1, 0] = some true ∧
    substitutionAutomaton letterMap false [0, 1] = some false ∧
    substitutionAutomaton letterMap false [1, 2] = none := by
  decide

end MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail
