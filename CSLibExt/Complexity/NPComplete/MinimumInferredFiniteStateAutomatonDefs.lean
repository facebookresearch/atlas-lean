/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED FINITE STATE AUTOMATON: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AL8] MINIMUM INFERRED
FINITE STATE AUTOMATON;
E. M. Gold, "Complexity of automaton identification from given data",
Information and Control 37 (1978), 302-320, doi:10.1016/S0019-9958(78)90562-4.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Computability.DFA

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton

/-- An instance: alphabet size `m` (letters `Fin m`), the strings `S` to accept, the strings
`T` to reject, and the state count `K`. -/
abbrev MinimumInferredFiniteStateAutomatonInstance :=
  ℕ × List (List ℕ) × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every letter of every string in `S` and `T` is below `m`,
and `K` is positive. -/
def WellFormed (i : MinimumInferredFiniteStateAutomatonInstance) : Prop :=
  (∀ w ∈ i.2.1, ∀ a ∈ w, a < i.1) ∧ (∀ w ∈ i.2.2.1, ∀ a ∈ w, a < i.1) ∧ 0 < i.2.2.2

/-- Some `DFA` with `K` states accepts every string of `S` and rejects every string of `T`. -/
def MinimumInferredFiniteStateAutomatonFeasible
    (i : MinimumInferredFiniteStateAutomatonInstance) : Prop :=
  ∃ A : DFA (Fin i.1) (Fin i.2.2.2),
    (∀ w : List (Fin i.1), w.map Fin.val ∈ i.2.1 → w ∈ A.accepts) ∧
      ∀ w : List (Fin i.1), w.map Fin.val ∈ i.2.2.1 → w ∉ A.accepts

open Classical in
/-- MINIMUM INFERRED FINITE STATE AUTOMATON as a decision problem over bitstrings. -/
noncomputable def minimumInferredFiniteStateAutomatonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumInferredFiniteStateAutomatonInstance) x with
  | some i => decide (WellFormed i ∧ MinimumInferredFiniteStateAutomatonFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton
