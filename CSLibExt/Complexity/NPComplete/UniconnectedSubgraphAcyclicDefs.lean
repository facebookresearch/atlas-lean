/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNICONNECTED SUBGRAPH for acyclic directed graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT30] UNICONNECTED SUBGRAPH, comment;
S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Technical Report
CU-CS-092-76, Department of Computer Science, University of Colorado, Boulder (1976),
p. 2 and Lemma 1, https://scholar.colorado.edu/concern/reports/rb68xc64n.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UniconnectedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraphAcyclic

open UniconnectedSubgraph (UniconnectedSubgraphInstance Graph UniconnectedSubgraphFeasible)

/-- Well-formedness of an instance: a well-formed UNICONNECTED SUBGRAPH instance (a loop-free arc
list without duplicates on `Fin n`, and `0 < K ≤ |A|`) whose digraph is acyclic: no vertex
reaches itself by a nonempty sequence of arcs. -/
def WellFormed (i : UniconnectedSubgraphInstance) : Prop :=
  UniconnectedSubgraph.WellFormed i ∧ ∀ v, ¬ Relation.TransGen (Graph i).Adj v v

open Classical in
/-- UNICONNECTED SUBGRAPH for acyclic directed graphs as a decision problem over bitstrings. -/
noncomputable def uniconnectedSubgraphAcyclicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniconnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ UniconnectedSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraphAcyclic
