/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Left quotients, prefixes, suffixes and infixes of regular and context-free languages
-/
module

public import CSLibExt.Computability.Languages.ContextFree.RightQuotient
public import CSLibExt.Computability.Languages.RegularQuotient

/-!
# Left quotients, prefixes, suffixes and infixes

Corollaries of the quotient closures `IsRegular.rightQuotientSet`, `IsRegular.leftQuotientSet`
(`RegularQuotient.lean`) and `IsContextFree.rightQuotientLang` (`ContextFree/RightQuotient.lean`):

* `IsContextFree.leftQuotientLang`: the left quotient `{y | ∃ x ∈ R, x ++ y ∈ L}` of a
  context-free language by a regular language is context-free, by reversal
  (`Language.IsContextFree.reverse`, `IsRegular.reverse`).
* The sets of prefixes `{x | ∃ y, x ++ y ∈ L}`, suffixes `{y | ∃ x, x ++ y ∈ L}` and infixes
  `{y | ∃ x z, x ++ y ++ z ∈ L}`: quotients by the language of all words. They are regular for
  regular `L` (`IsRegular.prefixes`, `IsRegular.suffixes`, `IsRegular.infixes`) and context-free
  for context-free `L` over a finite alphabet (`IsContextFree.prefixes`, `IsContextFree.suffixes`,
  `IsContextFree.infixes`).
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

theorem leftQuotient_eq_reverse_rightQuotientLang (L R : Language T) :
    ({y | ∃ x ∈ R, x ++ y ∈ L} : Language T) =
      (rightQuotientLang L.reverse R.reverse).reverse := by
  ext y
  change _ ↔ ∃ z, z.reverse ∈ R ∧ (y.reverse ++ z).reverse ∈ L
  simp only [List.reverse_append, List.reverse_reverse]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x.reverse, by rwa [List.reverse_reverse], by rwa [List.reverse_reverse]⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨z.reverse, hz, h⟩

/-- **The left quotient of a context-free language by a regular language is context-free**, over
a finite alphabet. -/
theorem IsContextFree.leftQuotientLang [Finite T] {L R : Language T} (hL : L.IsContextFree)
    (hR : R.IsRegular) : Language.IsContextFree {y | ∃ x ∈ R, x ++ y ∈ L} := by
  rw [leftQuotient_eq_reverse_rightQuotientLang]
  exact (IsContextFree.rightQuotientLang hL.reverse hR.reverse).reverse

theorem prefixes_eq (L : Language T) :
    ({x | ∃ y, x ++ y ∈ L} : Language T) = {x | ∃ y ∈ (⊤ : Language T), x ++ y ∈ L} := by
  ext x
  exact ⟨fun ⟨y, h⟩ => ⟨y, trivial, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩

theorem suffixes_eq (L : Language T) :
    ({y | ∃ x, x ++ y ∈ L} : Language T) = {y | ∃ x ∈ (⊤ : Language T), x ++ y ∈ L} := by
  ext y
  exact ⟨fun ⟨x, h⟩ => ⟨x, trivial, h⟩, fun ⟨x, _, h⟩ => ⟨x, h⟩⟩

theorem infixes_eq (L : Language T) :
    ({y | ∃ x z, x ++ y ++ z ∈ L} : Language T) =
      {y | ∃ x, x ++ y ∈ ({w | ∃ z, w ++ z ∈ L} : Language T)} := by
  ext y
  rfl

theorem IsRegular.prefixes {L : Language T} (hL : L.IsRegular) :
    Language.IsRegular {x | ∃ y, x ++ y ∈ L} := by
  rw [prefixes_eq]
  exact IsRegular.rightQuotientSet hL ⊤

theorem IsRegular.suffixes {L : Language T} (hL : L.IsRegular) :
    Language.IsRegular {y | ∃ x, x ++ y ∈ L} := by
  rw [suffixes_eq]
  exact IsRegular.leftQuotientSet hL ⊤

theorem IsRegular.infixes {L : Language T} (hL : L.IsRegular) :
    Language.IsRegular {y | ∃ x z, x ++ y ++ z ∈ L} := by
  rw [infixes_eq]
  exact IsRegular.suffixes (IsRegular.prefixes hL)

theorem IsContextFree.prefixes [Finite T] {L : Language T} (hL : L.IsContextFree) :
    Language.IsContextFree {x | ∃ y, x ++ y ∈ L} := by
  rw [prefixes_eq]
  exact IsContextFree.rightQuotientLang hL IsRegular.top

theorem IsContextFree.suffixes [Finite T] {L : Language T} (hL : L.IsContextFree) :
    Language.IsContextFree {y | ∃ x, x ++ y ∈ L} := by
  rw [suffixes_eq]
  exact IsContextFree.leftQuotientLang hL IsRegular.top

theorem IsContextFree.infixes [Finite T] {L : Language T} (hL : L.IsContextFree) :
    Language.IsContextFree {y | ∃ x z, x ++ y ++ z ∈ L} := by
  rw [infixes_eq]
  exact IsContextFree.suffixes (IsContextFree.prefixes hL)

end Cslib.Language
