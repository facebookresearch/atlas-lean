/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.RightQuotient
public import CSLibExt.Computability.Languages.Finite

/-!
# Tests for right quotients of context-free languages

* The right quotient of `{[true, false, true]}` by `{[true]}` is context-free and contains
  `[true, false]` and not `[true]`.
* With a two-word `R = {[false], [true]}`, `[true]` is in the quotient of `{[true, false]}`
  (some word of `R` works, not all).
* The quotient of a finite language by the infinite regular language `{[true]}∗` is
  context-free.
* The marking languages: `[inl true, inl false]` is a left word and `[inr true]` is a marked word
  of `{[true]}`; the generic statement is instantiated.
-/

@[expose] public section

namespace Cslib.Language.ContextFreeRightQuotientTests

example : (rightQuotientLang ({[true, false, true]} : Language Bool) {[true]}).IsContextFree :=
  IsContextFree.rightQuotientLang (IsContextFree.singleton_word _) (IsRegular.singleton_word _)

example : [true, false] ∈ rightQuotientLang ({[true, false, true]} : Language Bool) {[true]} :=
  ⟨[true], rfl, rfl⟩

example : [true] ∉ rightQuotientLang ({[true, false, true]} : Language Bool) {[true]} := by
  rintro ⟨y, hy, hxy⟩
  rw [Set.mem_singleton_iff.1 hy] at hxy
  simp at hxy

example : [true] ∈ rightQuotientLang ({[true, false]} : Language Bool) {[false], [true]} :=
  ⟨[false], Or.inl rfl, rfl⟩

example : (rightQuotientLang ({[true, false, true]} : Language Bool)
    (KStar.kstar {[true]})).IsContextFree :=
  IsContextFree.rightQuotientLang (IsContextFree.singleton_word _)
    (IsRegular.kstar (IsRegular.singleton_word _))

example : [Sum.inl true, Sum.inl false] ∈ (RightQuotientLang.leftWords : Language (Bool ⊕ Bool)) :=
  ⟨[true, false], rfl⟩

example : [Sum.inr true] ∈ RightQuotientLang.rightWords ({[true]} : Language Bool) :=
  ⟨[true], rfl, rfl⟩

example {T : Type} [Finite T] {L R : Language T} (hL : L.IsContextFree) (hR : R.IsRegular) :
    (rightQuotientLang L R).IsContextFree :=
  IsContextFree.rightQuotientLang hL hR

end Cslib.Language.ContextFreeRightQuotientTests
