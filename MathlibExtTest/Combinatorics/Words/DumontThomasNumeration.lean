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

-- The first digit skips a block of length two. Reversing the digits selects a different letter.
example : (morphIterate letterMap 2 [false])[2]? =
    substitutionAutomaton letterMap false [1, 0] := by
  have hη : IsSubstitution letterMap := by
    refine ⟨fun a => by cases a <;> decide, false, Filter.tendsto_atTop_atTop.mpr ?_⟩
    intro n
    refine ⟨n, fun k hk => ?_⟩
    have hlen (a : Bool) : (letterMap a).length = 2 := by cases a <;> rfl
    simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le
  have hadm : IsLetterAdmissibleSequence letterMap false path 1 := by
    refine ⟨fun i hi => ?_, ⟨[], rfl⟩⟩
    obtain rfl : i = 0 := by omega
    exact ⟨[false], rfl⟩
  exact morphIterate_getElem_eq_substitutionAutomaton_tail
    letterMap (hη := hη) 2 (hp := by decide) false path hadm

example : substitutionAutomaton letterMap false [1, 0] = some true ∧
    substitutionAutomaton letterMap false [0, 1] = some false ∧
    substitutionAutomaton letterMap false [1, 2] = none := by
  decide

end MetaMathlibExt.morphIterate_getElem_eq_substitutionAutomaton_tail
