/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM INFERRED FINITE STATE AUTOMATON for nearly complete samples: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 267, comment to problem [AL8]
MINIMUM INFERRED FINITE STATE AUTOMATON ("for any fixed ε > 0, the problem remains
NP-complete if restricted to instances for which (S ∪ T) ⊆ Σ^(n) and
|Σ^(n) - (S ∪ T)| ≤ |Σ^(n)|^ε", credited there to Angluin, 1977);
D. Angluin, "On the complexity of minimum inference of regular sets", Information
and Control 39 (1978), 337-350, doi:10.1016/S0019-9958(78)90683-6.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonNearlyComplete

open MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomaton

/-- `|Σ^(n)|` for an alphabet of `m` letters: the number of strings of length at most `n`. -/
def stringsUpTo (m n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), m ^ k

/-- The sample is nearly complete for `ε = p / q`: for some `n`, every string of `S` and `T`
has length at most `n`, and `|Σ^(n) - (S ∪ T)|^q ≤ |Σ^(n)|^p`. -/
def NearlyComplete (p q : ℕ) (i : MinimumInferredFiniteStateAutomatonInstance) : Prop :=
  ∃ n, (∀ w ∈ i.2.1 ++ i.2.2.1, w.length ≤ n) ∧
    (stringsUpTo i.1 n - (i.2.1 ++ i.2.2.1).toFinset.card) ^ q ≤ stringsUpTo i.1 n ^ p

/-- Well-formedness of an instance: it is a well-formed MINIMUM INFERRED FINITE STATE
AUTOMATON instance (letters below `m`, `K` positive), and the sample is nearly complete for
`ε = p / q`. -/
def WellFormed (p q : ℕ) (i : MinimumInferredFiniteStateAutomatonInstance) : Prop :=
  MinimumInferredFiniteStateAutomaton.WellFormed i ∧ NearlyComplete p q i

open Classical in
/-- MINIMUM INFERRED FINITE STATE AUTOMATON restricted to nearly complete samples for
`ε = p / q`, as a decision problem over bitstrings. -/
noncomputable def minimumInferredFiniteStateAutomatonNearlyCompleteDec (p q : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumInferredFiniteStateAutomatonInstance) x with
  | some i => decide (WellFormed p q i ∧ MinimumInferredFiniteStateAutomatonFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumInferredFiniteStateAutomatonNearlyComplete
