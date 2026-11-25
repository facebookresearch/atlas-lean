/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.ModelChecking

/-!
# LTL model checking as language inclusion

In the automata-theoretic approach, a finite-state program `P` is itself a Büchi automaton
`A_P` whose states are all accepting and whose language is the set of computations of `P`;
then `P` satisfies `φ` iff `L(A_P) ⊆ L(A_φ)`, iff `L(A_P) ∩ L(A_¬φ) = ∅`. The second form is
`Cslib.LTL.ModelChecking.models_iff_language_empty`; this file adds the automaton `A_P` and
the inclusion form.

Here, as in `CSLibExt.Logics.LTL.ModelChecking`, the letter read at each step is the current
state of the transition system and the valuation is on states; Vardi's `A_P` reads the label
`V(s)` instead, which is the special case `valuation s p := p ∈ V s`.

* `Cslib.LTL.ModelChecking.systemAutomaton`: the Büchi automaton `A_P` of a transition system.
* `Cslib.LTL.ModelChecking.mem_systemAutomaton_iff`: its language is the set of initial
  infinite runs.
* `Cslib.LTL.ModelChecking.models_iff_language_le`: model checking is language inclusion.
* `Cslib.LTL.ModelChecking.models_iff_inf_language_neg_eq_bot`: model checking is emptiness
  of the intersection with the language of the negated formula.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Section 4.2 (author's posted version `banff94rj.pdf`).
* M. Y. Vardi and P. Wolper, "An automata-theoretic approach to automatic program
  verification", LICS 1986, 332-344.
-/

@[expose] public section

namespace Cslib.LTL.ModelChecking

open Automata.NA Automata.ωAcceptor Filter

variable {State Action Atom : Type*}

/-- **Büchi automaton of a transition system.** The automaton reads the current state as its
letter, moves along a transition of the system and accepts every infinite run: all states
are accepting, as in the automaton `A_P` of Vardi, "An automata-theoretic approach to linear
temporal logic" (LNCS 1043, 1996), Section 4.2. -/
def systemAutomaton (lts : LTS State Action) (initial : Set State) : Buchi State State where
  Tr s x t := x = s ∧ ∃ action, lts.Tr s action t
  start := initial
  accept := Set.univ

/-- **The language of the system automaton is the set of runs.** An infinite sequence of
states is accepted by `systemAutomaton lts initial` iff it is an initial infinite run of the
transition system. -/
theorem mem_systemAutomaton_iff (lts : LTS State Action) (initial : Set State)
    (w : ωSequence State) :
    w ∈ language (systemAutomaton lts initial) ↔ IsRun lts initial w := by
  rw [isRun_iff]
  constructor
  · rintro ⟨ss, hrun, -⟩
    have heq : ∀ n, w n = ss n := fun n => (hrun.trans n).1
    refine ⟨?_, fun n => ?_⟩
    · rw [heq 0]; exact hrun.start
    · rw [heq n, heq (n + 1)]; exact (hrun.trans n).2
  · rintro ⟨hstart, hsteps⟩
    exact ⟨w, ⟨hstart, fun n => ⟨rfl, hsteps n⟩⟩,
      Frequently.of_forall fun _ => Set.mem_univ _⟩

/-- **LTL model checking is language inclusion.** All initial infinite runs of a transition
system satisfy `φ` iff the language of the system automaton is contained in the language of
the Büchi automaton of `φ` (Vardi, "An automata-theoretic approach to linear temporal logic",
LNCS 1043, 1996, Section 4.2: `L_ω(A_P) ⊆ L_ω(A_φ)`). -/
theorem models_iff_language_le (lts : LTS State Action) (initial : Set State)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Models lts initial valuation φ ↔
      language (systemAutomaton lts initial) ≤ language (Tableau.buchi valuation φ) := by
  constructor
  · intro h w hw
    exact (Tableau.mem_buchi_iff valuation φ w).mpr
      (h w ((mem_systemAutomaton_iff lts initial w).mp hw))
  · intro h w hrun
    exact (Tableau.mem_buchi_iff valuation φ w).mp
      (h ((mem_systemAutomaton_iff lts initial w).mpr hrun))

/-- **LTL model checking is emptiness of an intersection.** All initial infinite runs of a
transition system satisfy `φ` iff no word is accepted both by the system automaton and by the
Büchi automaton of `¬φ`; the automaton of the negated formula replaces the complement of the
automaton of `φ` (Vardi, "An automata-theoretic approach to linear temporal logic", LNCS
1043, 1996, Section 4.2: `L_ω(A_P) ∩ L_ω(A_¬φ) = ∅`). -/
theorem models_iff_inf_language_neg_eq_bot (lts : LTS State Action) (initial : Set State)
    (valuation : State → Atom → Prop) (φ : Formula Atom) :
    Models lts initial valuation φ ↔
      language (systemAutomaton lts initial) ⊓ language (Tableau.buchi valuation (.not φ)) =
        ⊥ := by
  rw [models_iff_language_empty]
  constructor
  · intro h
    apply ωLanguage.mem_ext
    intro w
    change (w ∈ language (systemAutomaton lts initial) ∧
      w ∈ language (Tableau.buchi valuation (.not φ))) ↔ w ∈ (⊥ : ωLanguage State)
    rw [← h, mem_systemAutomaton_iff]
    exact (mem_product_iff lts initial (Tableau.buchi valuation (.not φ)) w).symm
  · intro h
    apply ωLanguage.mem_ext
    intro w
    change w ∈ language (product lts initial (Tableau.buchi valuation (.not φ))) ↔ _
    rw [mem_product_iff, ← mem_systemAutomaton_iff lts initial w, ← h]
    rfl

end Cslib.LTL.ModelChecking
