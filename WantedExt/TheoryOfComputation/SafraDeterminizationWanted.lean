/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Safra/Piterman determinization of Büchi automata
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Foundations.Data.OmegaSequence.Parity
public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

namespace Cslib.SafraDeterminizationWanted

open Cslib.Automata.NA
open Cslib.Automata.ωAcceptor

/-!
# Safra/Piterman determinization of Büchi automata

Safra's construction turns a nondeterministic Büchi automaton into a
deterministic Rabin automaton; Piterman's refinement turns it into a
deterministic parity automaton with `2^O(n log n)` states. The statement below
is this state bound, made explicit through a universal constant `c` (as in
`Cslib.BuchiComplementationWanted.buchi_complement_bounded_wanted`); it does not
bound the priorities.
-/

/-- A deterministic parity automaton: a single start state, a deterministic
transition function, and a priority for each state. Its language is the set of
words whose unique run satisfies the max-parity condition. -/
structure DetParity (State Symbol : Type*) where
  /-- The unique start state. -/
  start : State
  /-- The deterministic transition function. -/
  trans : State → Symbol → State
  /-- The priority of each state. -/
  priority : State → ℕ

namespace DetParity

variable {State Symbol : Type*}

/-- The unique run of a deterministic parity automaton on a word. -/
def run (d : DetParity State Symbol) (xs : ωSequence Symbol) : ℕ → State
  | 0 => d.start
  | n + 1 => d.trans (run d xs n) (xs n)

/-- The language of a deterministic parity automaton: the words whose unique run
has even maximal recurring priority. -/
def language (d : DetParity State Symbol) : ωLanguage Symbol :=
  {xs | Cslib.ωSequence.ParityEven (((run d xs : ℕ → State) : ωSequence State).map
    d.priority)}

end DetParity

/-- Source: S. Safra, "On the complexity of ω-automata", *Proceedings of FOCS
1988*, 319-327 (determinization to deterministic Rabin); N. Piterman, "From
nondeterministic Büchi and Streett automata to deterministic parity automata",
*Proceedings of LICS 2006*, 255-264, and "From nondeterministic Büchi and
Streett automata to deterministic parity automata", *Logical Methods in Computer
Science* 3 (2007) (deterministic parity automata with `2^O(n log n)`
states). -/
public theorem_wanted safra_piterman_wanted :
    ∃ c : ℕ, ∀ (n k : ℕ) (a : Buchi (Fin n) (Fin k)),
      ∃ m : ℕ, m ≤ 2 ^ (c * n * (Nat.log2 (n + 1) + 1)) ∧
        ∃ d : DetParity (Fin m) (Fin k), d.language = language a

end Cslib.SafraDeterminizationWanted
