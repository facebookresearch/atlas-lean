/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Languages.OmegaRegularLanguage

/-!
# Boolean closure of Büchi automata

Upstream CSLib proves that ω-regular languages (`Cslib.ωLanguage.IsRegular`: languages of
finite-state nondeterministic Büchi automata) are closed under union
(`Cslib.ωLanguage.IsRegular.sup`, by the disjoint sum of automata), intersection
(`Cslib.ωLanguage.IsRegular.inf`, by the product with a pointer to the track that must next
visit an accepting state) and complement (`Cslib.ωLanguage.IsRegular.compl`, by Büchi's
congruence of finite index). This file restates these facts in the automaton form used in
the automata-theoretic approach to verification, and removes the `Inhabited` alphabet
assumption of the upstream complementation theorem: over an empty alphabet there are no
infinite words, so every ω-language is empty and trivially ω-regular. Vardi's notes, like
Büchi, work over a finite nonempty alphabet; the statements here drop both conditions (the
empty case is trivial, the infinite case is covered by upstream CSLib).

* `Cslib.Automata.NA.Buchi.exists_buchi_sup`: union (Vardi, Proposition 5).
* `Cslib.Automata.NA.Buchi.exists_buchi_inf`: intersection (Vardi, Proposition 6).
* `Cslib.ωLanguage.IsRegular.compl_any`: complement of an ω-regular language, any
  alphabet.
* `Cslib.Automata.NA.Buchi.exists_buchi_compl`: complementation (Vardi, Proposition 7).

No bound on the number of states is claimed: the upstream complementation goes through
Büchi's congruence and is not the `2^{O(n log n)}` construction.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Section 2.2 (author's posted version `banff94rj.pdf`).
* J. R. Büchi, "On a decision method in restricted second order arithmetic", Proc. Int.
  Congress on Logic, Methodology and Philosophy of Science 1960, Stanford, 1962.
-/

@[expose] public section

namespace Cslib.ωLanguage

/-- **Complement of an ω-regular language, over any alphabet.** If `p` is recognized by a
finite-state nondeterministic Büchi automaton, so is its complement. Unlike the upstream
`Cslib.ωLanguage.IsRegular.compl`, the alphabet need not be inhabited: over an empty alphabet
there are no infinite words, so the complement is the empty language. Büchi (1962); Vardi,
"An automata-theoretic approach to linear temporal logic" (LNCS 1043, 1996), Proposition 7,
both for a finite nonempty alphabet, which this statement does not require. -/
theorem IsRegular.compl_any {Symbol : Type} {p : ωLanguage Symbol}
    (h : p.IsRegular) : (pᶜ).IsRegular := by
  rcases isEmpty_or_nonempty Symbol with hS | hS
  · have : pᶜ = ⊥ := ωLanguage.mem_ext fun xs => isEmptyElim (xs 0)
    rw [this]
    exact IsRegular.bot
  · have : Inhabited Symbol := Classical.inhabited_of_nonempty hS
    exact h.compl

end Cslib.ωLanguage

namespace Cslib.Automata.NA.Buchi

open ωAcceptor

/-- **Büchi automata are closed under union.** For finite-state nondeterministic Büchi
automata `a₁` and `a₂` over the same alphabet, some finite-state nondeterministic Büchi
automaton accepts exactly the infinite words accepted by `a₁` or by `a₂` (Vardi, "An
automata-theoretic approach to linear temporal logic", LNCS 1043, 1996, Proposition 5,
credited there to Choueka 1974). -/
theorem exists_buchi_sup {Symbol : Type*} {S₁ S₂ : Type} [Finite S₁] [Finite S₂]
    (a₁ : Buchi S₁ Symbol) (a₂ : Buchi S₂ Symbol) :
    ∃ (S : Type) (_ : Finite S) (a : Buchi S Symbol),
      language a = language a₁ ⊔ language a₂ :=
  ωLanguage.IsRegular.sup ⟨S₁, inferInstance, a₁, rfl⟩ ⟨S₂, inferInstance, a₂, rfl⟩

/-- **Büchi automata are closed under intersection.** For finite-state nondeterministic
Büchi automata `a₁` and `a₂` over the same alphabet, some finite-state nondeterministic Büchi
automaton accepts exactly the infinite words accepted by both (Vardi, "An automata-theoretic
approach to linear temporal logic", LNCS 1043, 1996, Proposition 6, credited there to Choueka
1974). The upstream construction is a variant of the product with a two-valued pointer of that
proposition; the plain product with accepting set `F₁ × F₂` would not do. -/
theorem exists_buchi_inf {Symbol : Type*} {S₁ S₂ : Type} [Finite S₁] [Finite S₂]
    (a₁ : Buchi S₁ Symbol) (a₂ : Buchi S₂ Symbol) :
    ∃ (S : Type) (_ : Finite S) (a : Buchi S Symbol),
      language a = language a₁ ⊓ language a₂ :=
  ωLanguage.IsRegular.inf ⟨S₁, inferInstance, a₁, rfl⟩ ⟨S₂, inferInstance, a₂, rfl⟩

/-- **Büchi automata are closed under complementation.** For every finite-state
nondeterministic Büchi automaton `a`, some finite-state nondeterministic Büchi automaton
accepts exactly the infinite words that `a` rejects (Büchi 1962; Vardi, "An automata-theoretic
approach to linear temporal logic", LNCS 1043, 1996, Proposition 7, both over a finite nonempty
alphabet). Here no assumption is made on the alphabet. No bound on the number of states is
claimed. -/
theorem exists_buchi_compl {Symbol S : Type} [Finite S] (a : Buchi S Symbol) :
    ∃ (S' : Type) (_ : Finite S') (a' : Buchi S' Symbol), language a' = (language a)ᶜ :=
  ωLanguage.IsRegular.compl_any ⟨S, inferInstance, a, rfl⟩

end Cslib.Automata.NA.Buchi
