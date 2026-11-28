/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on k-regular Hamiltonian graphs (k ≥ 4): definitions

Source:
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Section 3.3, Theorem 3.29
(and Theorem 3.30 for `k = 5`, Theorem 3.5 for `k = 4`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment; the parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"5-regular ∩ hamiltonian" (gc_1317), problem Feedback vertex set: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetRegularHamiltonian

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

open Classical in
/-- Well-formedness of an instance for a fixed `k`: a well-formed FEEDBACK VERTEX SET instance
(a simple edge list on `Fin n`) whose graph is `k`-regular and has a Hamiltonian cycle. -/
def WellFormed (k : ℕ) (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ (Graph i).IsRegularOfDegree k ∧
    ∃ (a : Fin i.1) (p : (Graph i).Walk a a), p.IsHamiltonianCycle

open Classical in
/-- FEEDBACK VERTEX SET on `k`-regular Hamiltonian graphs as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetRegularHamiltonianDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed k i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetRegularHamiltonian
