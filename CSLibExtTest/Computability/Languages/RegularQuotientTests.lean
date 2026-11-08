/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.RegularQuotient
public import CSLibExt.Computability.Languages.Congruences.Quotients

/-!
# Tests for quotients of regular languages by arbitrary languages

* `endsTrueDFA` accepts the words ending in `true`. Its right quotient by `{[true]}` contains
  `[false]`; its left quotient by `{[false]}` contains `[true]` and not `[]`.
* The quotients by a single word are the special cases `R = {w}`: Mathlib's
  `Language.leftQuotient` and CSLibExt's `rightQuotient`.
-/

@[expose] public section

namespace Cslib.Language.RegularQuotientTests

/-- The last letter read; accepts the words ending in `true`. -/
def endsTrueDFA : DFA Bool Bool :=
  ⟨fun _ b => b, false, {true}⟩

example : Language.IsRegular
    ({x | ∃ y ∈ ({[true]} : Language Bool), x ++ y ∈ endsTrueDFA.accepts} : Language Bool) :=
  IsRegular.rightQuotientSet ⟨Bool, inferInstance, endsTrueDFA, rfl⟩ _

example : [false] ∈
    (RegularQuotient.rightDFA endsTrueDFA ({[true]} : Language Bool)).accepts := by
  rw [RegularQuotient.rightDFA_accepts]
  exact ⟨[true], rfl, rfl⟩

example : [true] ∈ (RegularQuotient.leftNFA endsTrueDFA ({[false]} : Language Bool)).accepts := by
  rw [RegularQuotient.leftNFA_accepts]
  exact ⟨[false], rfl, rfl⟩

example : [] ∉ (RegularQuotient.leftNFA endsTrueDFA ({[false]} : Language Bool)).accepts := by
  rw [RegularQuotient.leftNFA_accepts]
  rintro ⟨x, hx, h⟩
  rw [Set.mem_singleton_iff.1 hx] at h
  exact absurd (show (false : Bool) ∈ ({true} : Set Bool) from h) (by simp)

/-- The left quotient by a word is the special case `R = {pre}`. -/
example {L : Language Bool} (hL : L.IsRegular) (pre : List Bool) :
    (L.leftQuotient pre).IsRegular := by
  have e : L.leftQuotient pre =
      ({y | ∃ x ∈ ({pre} : Language Bool), x ++ y ∈ L} : Language Bool) := by
    ext y
    constructor
    · intro h
      exact ⟨pre, rfl, h⟩
    · rintro ⟨x, rfl, h⟩
      exact h
  rw [e]
  exact IsRegular.leftQuotientSet hL _

/-- The right quotient by a word is the special case `R = {suffix}`. -/
example {L : Language Bool} (hL : L.IsRegular) (suffix : List Bool) :
    (rightQuotient L suffix).IsRegular := by
  have e : rightQuotient L suffix =
      ({x | ∃ y ∈ ({suffix} : Language Bool), x ++ y ∈ L} : Language Bool) := by
    ext x
    constructor
    · intro h
      exact ⟨suffix, rfl, h⟩
    · rintro ⟨y, rfl, h⟩
      exact h
  rw [e]
  exact IsRegular.rightQuotientSet hL _

end Cslib.Language.RegularQuotientTests
