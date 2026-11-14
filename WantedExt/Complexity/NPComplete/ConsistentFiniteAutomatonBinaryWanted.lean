/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENT FINITE AUTOMATON over a binary alphabet is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem [AL1] MINIMUM CONSISTENT FINITE AUTOMATON (binary strings; Garey and Johnson
[AL8] for a general alphabet);
J. Lingg, M. de Oliveira Oliveira and P. Wolf, "Learning from positive and negative examples:
New proof for binary alphabets", Information Processing Letters 184 (2024), 106427,
doi:10.1016/j.ipl.2023.106427;
E. M. Gold, "Complexity of automaton identification from given data",
Information and Control 37 (1978), 302-320, doi:10.1016/S0019-9958(78)90562-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistentFiniteAutomatonBinary

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton

/-!
# CONSISTENT FINITE AUTOMATON over a binary alphabet is NP-complete

INSTANCE: two finite sets `P, N` of binary strings and a positive integer `K`.
QUESTION: is there a deterministic finite automaton `(Q, {0, 1}, δ, q₀, F)` with at most `K`
states that accepts all strings in `P` and rejects all strings in `N`?

This is the restriction of MINIMUM INFERRED FINITE STATE AUTOMATON
(`WantedExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonWanted`, Garey and Johnson
[AL8]) to the alphabet `{0, 1}`. Lingg, de Oliveira Oliveira and Wolf (2024) state the DFA
consistency problem with input "two sets of strings `P` and `N`, and an integer `k`", ask
"if there is a DFA with at most `k` states that accepts all strings in `P` and rejects all
strings in `N`", and prove it NP-complete on binary alphabets; their abstract explains that
Gold's (1978) results are stated for Mealy machines and that the adaptations of his
construction to binary DFAs in the literature have issues.

The instance is `P`, `N` and `K`; `withBinaryAlphabet` puts the alphabet size `2` in front to
obtain an instance of MINIMUM INFERRED FINITE STATE AUTOMATON, whose `WellFormed` (every letter
below the alphabet size, here `0` or `1`, and `0 < K`) and
`MinimumInferredFiniteStateAutomatonFeasible` (a Mathlib `DFA (Fin 2) (Fin K)` accepting `P`
and rejecting `N`) are reused unchanged. A DFA with at most `K` states exists exactly when one
with exactly `K` states does, by adding unreachable states. `K` is positive as in Crescenzi
and Kann's decision version and Garey and Johnson's [AL8]; no DFA has `0` states.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the strings `P` to accept and `N` to reject, as lists of letters `0` and `1`,
and the state bound `K`. -/
abbrev ConsistentFiniteAutomatonBinaryInstance := List (List ℕ) × List (List ℕ) × ℕ

/-- The MINIMUM INFERRED FINITE STATE AUTOMATON instance with alphabet `{0, 1}` and the same
`P`, `N` and `K`. -/
abbrev withBinaryAlphabet (i : ConsistentFiniteAutomatonBinaryInstance) :
    MinimumInferredFiniteStateAutomatonInstance :=
  (2, i.1, i.2.1, i.2.2)

open Classical in
/-- CONSISTENT FINITE AUTOMATON over a binary alphabet as a decision problem over bitstrings. -/
noncomputable def consistentFiniteAutomatonBinaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConsistentFiniteAutomatonBinaryInstance) x with
  | some i => decide (WellFormed (withBinaryAlphabet i) ∧
      MinimumInferredFiniteStateAutomatonFeasible (withBinaryAlphabet i))
  | none => false

/-- **CONSISTENT FINITE AUTOMATON over a binary alphabet is NP-complete.** Source: Crescenzi and
Kann (2000), [AL1]; Lingg, de Oliveira Oliveira and Wolf (2024). -/
public theorem_wanted consistentFiniteAutomatonBinary_npComplete :
    consistentFiniteAutomatonBinaryDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consistentFiniteAutomatonBinaryDec

end MetaMathlibExt.Complexity.NPComplete.ConsistentFiniteAutomatonBinary
