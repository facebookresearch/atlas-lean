/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on planar 4-regular Hamiltonian graphs: definitions

Source:
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 3.5;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment; the parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"4-regular ∩ hamiltonian ∩ planar" (gc_1315), problem Feedback vertex set: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetPlanarDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanarFourRegularHamiltonian

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed instance of FEEDBACK VERTEX SET on planar
graphs (a simple edge list on `Fin n`, a planar graph, `0 < K ≤ n`) whose graph is 4-regular
and Hamiltonian. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSetPlanar.WellFormed i ∧ (Graph i).IsRegularOfDegree 4 ∧ (Graph i).IsHamiltonian

open Classical in
/-- FEEDBACK VERTEX SET on planar 4-regular Hamiltonian graphs as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetPlanarFourRegularHamiltonianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPlanarFourRegularHamiltonian
