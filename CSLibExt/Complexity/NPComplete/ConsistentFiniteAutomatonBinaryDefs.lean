/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENT FINITE AUTOMATON over a binary alphabet: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM CONSISTENT FINITE AUTOMATON (binary strings; Garey and Johnson
[AL8] for a general alphabet);
J. Lingg, M. de Oliveira Oliveira and P. Wolf, "Learning from positive and negative examples:
New proof for binary alphabets", Information Processing Letters 184 (2024), 106427,
doi:10.1016/j.ipl.2023.106427;
E. M. Gold, "Complexity of automaton identification from given data",
Information and Control 37 (1978), 302-320, doi:10.1016/S0019-9958(78)90562-4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistentFiniteAutomatonBinary

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton

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

end MetaMathlibExt.Complexity.NPComplete.ConsistentFiniteAutomatonBinary
