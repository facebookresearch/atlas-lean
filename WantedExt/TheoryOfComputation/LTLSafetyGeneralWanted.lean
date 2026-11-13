/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Büchi automata for the general LTL safety fragment (`G` of a safety formula)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.LTL.FragmentBuchi

@[expose] public section

namespace Cslib.LTL.SafetyGeneralWanted

open Filter ωSequence Cslib.Automata.ωAcceptor
open Cslib.LTL

variable {Atom : Type*}

/-!
# Büchi automata for the general LTL safety fragment

The restricted safety fragment `Cslib.LTL.Safety` (`CSLibExt/Logics/LTL/
FragmentBuchi.lean`) has `always` only for propositional formulas. The general
safety fragment `SafetyExt` below adds `always` applied to an arbitrary safety
formula, closing the omitted scope of BACKLOG B19 (e.g. `G (p ∨ X q)`, `G (ψ ∨ ρ)`,
`G (X ψ)`): `G` does not distribute over `∨`, so the general case needs a
construction for `G` of a disjunction.

The construction is the safety-automaton + powerset-of-copies argument
(Kupferman-Vardi): every safety formula has a finite-state *safety* automaton,
an automaton with all states accepting whose language is the set of words with
an infinite run. For `G ψ`, the automaton tracks, for every suffix, the set of
states of the `ψ`-automaton reachable by runs on that suffix (one copy per
suffix, each copy a set of states); a transition is enabled exactly when no
copy dies, i.e. when every suffix still has a live run. The powerset-of-copies
state space is the finite set of sets of copies. The hard direction (a copy
whose reachable set stays nonempty for all steps has an infinite run) is
König's lemma for the finitely branching run tree.
-/

/-- The general safety fragment of LTL: propositional formulas, conjunction,
disjunction, next, and `always` applied to an arbitrary safety formula. -/
inductive SafetyExt (Atom : Type*) where
  /-- A propositional formula, checked on the first letter. -/
  | prop (φ : PropFormula Atom) : SafetyExt Atom
  /-- Conjunction. -/
  | and (ψ ρ : SafetyExt Atom) : SafetyExt Atom
  /-- Disjunction. -/
  | or (ψ ρ : SafetyExt Atom) : SafetyExt Atom
  /-- Next. -/
  | next (ψ : SafetyExt Atom) : SafetyExt Atom
  /-- `always` of a safety formula. -/
  | always (ψ : SafetyExt Atom) : SafetyExt Atom

namespace SafetyExt

/-- A general safety formula as an LTL formula. -/
def toLTL : SafetyExt Atom → Formula Atom
  | .prop φ => φ.toLTL
  | .and ψ ρ => .and ψ.toLTL ρ.toLTL
  | .or ψ ρ => Formula.or ψ.toLTL ρ.toLTL
  | .next ψ => .next ψ.toLTL
  | .always ψ => Formula.always ψ.toLTL

end SafetyExt

/-- **Büchi automata for the general safety fragment.** Every general safety formula
has a nondeterministic Büchi automaton with finitely many states and with the same
ω-language. Source: O. Kupferman and M. Y. Vardi, "Model checking of safety properties",
*Formal Methods in System Design* 19 (2001), 291-314 (safety automata and the
powerset-of-copies construction for `G`); M. Y. Vardi and P. Wolper, "An
automata-theoretic approach to automatic program verification", *Proceedings of LICS
1986*, 332-344 (the tableau construction). -/
public theorem_wanted safety_general_buchi_wanted :
    ∀ {Atom : Type*} (ψ : SafetyExt Atom),
      ∃ (S : Type) (_ : Finite S) (a : Cslib.Automata.NA.Buchi S (Set Atom)),
        Cslib.Automata.ωAcceptor.language a = Word.language (fun s a => a ∈ s) ψ.toLTL

end Cslib.LTL.SafetyGeneralWanted
