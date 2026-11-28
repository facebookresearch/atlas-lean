/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibExt.Combinatorics.Words.DumontThomasAcceptedWords

namespace MetaMathlibExt

private def letterMap : Bool → List Bool
  | false => [false, true]
  | true => [false, false]

private theorem letterMap_isSubstitution : IsSubstitution letterMap := by
  refine ⟨fun a => by cases a <;> decide, false, Filter.tendsto_atTop_atTop.mpr ?_⟩
  intro n
  refine ⟨n, fun k hk => ?_⟩
  have hlen (a : Bool) : (letterMap a).length = 2 := by cases a <;> rfl
  simpa [morphIterate_length_of_uniform hlen] using hk.trans (Nat.lt_two_pow_self (n := k)).le

-- At depth one the only pair is read directly from the seed's image.
example : ∃ s, IsLetterAdmissibleSequence letterMap false s 0 ∧ (s 0).1.length = 1 := by
  obtain ⟨s, hs, hdigit⟩ := exists_letterAdmissibleSequence_of_accepted
    letterMap letterMap_isSubstitution 1 (by decide) false (fun _ => 1) (by decide)
  exact ⟨s, hs, hdigit 0 (by decide)⟩

-- Reading [1, 0] visits true then false; [0, 1] would visit false then true.
example : ∃ s, IsLetterAdmissibleSequence letterMap false s 1 ∧
    (s 0).1.length = 0 ∧ (s 1).1.length = 1 ∧ (s 0).2 = false ∧ (s 1).2 = true := by
  obtain ⟨s, hs, hdigit⟩ := exists_letterAdmissibleSequence_of_accepted
    letterMap letterMap_isSubstitution 2 (by decide) false id (by decide)
  have h₀ : (s 0).1.length = 0 := hdigit 0 (by decide)
  have h₁ : (s 1).1.length = 1 := hdigit 1 (by decide)
  have hrun := substitutionAutomaton_admissibleSequence
    letterMap letterMap_isSubstitution 2 (by decide) false s hs
  have ha₀ := hrun 0 (by decide)
  have ha₁ := hrun 1 (by decide)
  change substitutionAutomaton letterMap false [(s 1).1.length, (s 0).1.length] = _ at ha₀
  change substitutionAutomaton letterMap false [(s 1).1.length] = _ at ha₁
  rw [h₁, h₀, show substitutionAutomaton letterMap false [1, 0] = some false by decide] at ha₀
  rw [h₁, show substitutionAutomaton letterMap false [1] = some true by decide] at ha₁
  exact ⟨s, hs, h₀, h₁, (Option.some.inj ha₀).symm, (Option.some.inj ha₁).symm⟩

end MetaMathlibExt
