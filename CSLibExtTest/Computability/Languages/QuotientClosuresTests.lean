/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.QuotientClosures
public import CSLibExt.Computability.Languages.Finite

/-!
# Tests for left quotients, prefixes, suffixes and infixes

* The left quotient of `{[true, false]}` by `{[true]}` is context-free and contains `[false]`.
* For `{[true, false, true]}`: the prefixes, suffixes and infixes are regular and context-free,
  and contain `[true, false]`, `[false, true]` and `[false]` respectively.
* The generic statements are instantiated.
-/

@[expose] public section

namespace Cslib.Language.QuotientClosuresTests

/-- The one-word language `{[true, false, true]}`. -/
abbrev w : Language Bool := {[true, false, true]}

example : Language.IsContextFree
    {y | ∃ x ∈ ({[true]} : Language Bool), x ++ y ∈ ({[true, false]} : Language Bool)} :=
  IsContextFree.leftQuotientLang (IsContextFree.singleton_word _) (IsRegular.singleton_word _)

example : [false] ∈
    ({y | ∃ x ∈ ({[true]} : Language Bool), x ++ y ∈ ({[true, false]} : Language Bool)} :
      Language Bool) :=
  ⟨[true], rfl, rfl⟩

example : Language.IsRegular {x | ∃ y, x ++ y ∈ w} :=
  IsRegular.prefixes (IsRegular.singleton_word _)

example : Language.IsRegular {y | ∃ x, x ++ y ∈ w} :=
  IsRegular.suffixes (IsRegular.singleton_word _)

example : Language.IsRegular {y | ∃ x z, x ++ y ++ z ∈ w} :=
  IsRegular.infixes (IsRegular.singleton_word _)

example : Language.IsContextFree {y | ∃ x z, x ++ y ++ z ∈ w} :=
  IsContextFree.infixes (IsContextFree.singleton_word _)

example : [true, false] ∈ ({x | ∃ y, x ++ y ∈ w} : Language Bool) :=
  ⟨[true], rfl⟩

example : [false, true] ∈ ({y | ∃ x, x ++ y ∈ w} : Language Bool) :=
  ⟨[true], rfl⟩

example : [false] ∈ ({y | ∃ x z, x ++ y ++ z ∈ w} : Language Bool) :=
  ⟨[true], [true], rfl⟩

example {T : Type} [Finite T] {L R : Language T} (hL : L.IsContextFree) (hR : R.IsRegular) :
    Language.IsContextFree {y | ∃ x ∈ R, x ++ y ∈ L} :=
  IsContextFree.leftQuotientLang hL hR

example {T : Type} [Finite T] {L : Language T} (hL : L.IsContextFree) :
    Language.IsContextFree {x | ∃ y, x ++ y ∈ L} ∧ Language.IsContextFree {y | ∃ x, x ++ y ∈ L} :=
  ⟨IsContextFree.prefixes hL, IsContextFree.suffixes hL⟩

end Cslib.Language.QuotientClosuresTests
