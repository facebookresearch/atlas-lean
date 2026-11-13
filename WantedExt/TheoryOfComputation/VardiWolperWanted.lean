/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Full LTL-to-Büchi translation (Vardi-Wolper)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.LTL.OmegaWord
public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

namespace Cslib.VardiWolperWanted

open Cslib.Automata.NA
open Cslib.Automata.ωAcceptor

/-!
# Full LTL-to-Büchi translation (Vardi-Wolper)

Every LTL formula is accepted by a nondeterministic Büchi automaton with the
same ω-language, over the alphabet `Set Atom` of atom valuations. The
tableau/closure construction of Vardi and Wolper builds the automaton from the
subformulas of the given formula (states are sets of subformulas, acceptance is
the generalized Büchi condition, degeneralized by a counter). This is the full
construction; the safety fragment and the `G F` / `F G` cases for propositional
formulas are proved in `CSLibExt.Logics.LTL.FragmentBuchi`
(`Cslib.LTL.exists_buchi_of_safety`,
`Cslib.LTL.language_always_eventually`,
`Cslib.LTL.language_eventually_always`).
-/

/-- The size of an LTL formula (the number of connective occurrences plus the
number of atoms), an upper bound on the number of distinct subformulas. The
Vardi-Wolper tableau states are consistent subsets of the closure (subformulas
and their negations), so there are at most `2 ^ (2 * formulaSize φ)` of them.
Source: M. Y. Vardi and P. Wolper, "An automata-theoretic approach to automatic
program verification", *Proceedings of LICS 1986*, 332-344. -/
def formulaSize {Atom : Type} : Cslib.LTL.Formula Atom → ℕ
  | .atom _ => 1
  | .top => 1
  | .not φ => formulaSize φ + 1
  | .and φ ψ => formulaSize φ + formulaSize ψ + 1
  | .next φ => formulaSize φ + 1
  | .until φ ψ => formulaSize φ + formulaSize ψ + 1

/-- Source: M. Y. Vardi and P. Wolper, "An automata-theoretic approach to
automatic program verification", *Proceedings of LICS 1986*, 332-344 (the
closure/tableau construction; states are sets of subformulas). The state type
is finite: the construction has at most `2 ^ (2 * formulaSize φ)` states
(subsets of the closure), so the statement is the finite-automaton theorem,
not the trivial unrestricted-state one. -/
public theorem_wanted vardi_wolper_wanted :
    ∀ {Atom : Type} (φ : Cslib.LTL.Formula Atom),
      ∃ (S : Type) (_ : Finite S) (a : Buchi S (Set Atom)),
        language a = Cslib.LTL.Word.language (fun s a => a ∈ s) φ ∧
          Nat.card S ≤ 2 ^ (2 * formulaSize φ)

end Cslib.VardiWolperWanted
