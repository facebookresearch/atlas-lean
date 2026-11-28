/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBFOREST ISOMORPHISM: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), Section 4.2, Theorem 4.6 ("SUBFOREST
ISOMORPHISM is NP-complete"), pp. 104-106, and problem [GT48] SUBGRAPH ISOMORPHISM, p. 202
(comment: "remains NP-complete if `G` is a tree and `H` is a forest (see Chapter 4)").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.SubgraphIsomorphismDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubforestIsomorphism

open MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
  (SubgraphIsomorphismInstance GraphHost)

/-- Well-formedness of an instance: it is a well-formed SUBGRAPH ISOMORPHISM instance (both edge
lists simple), the host `G` is a tree, and the pattern `H`, the graph
`Cslib.Complexity.Karp.edgeGraph |V₂| E₂`, is a forest. -/
def WellFormed (i : SubgraphIsomorphismInstance) : Prop :=
  SubgraphIsomorphism.WellFormed i ∧ (GraphHost i).IsTree ∧
    (Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2).IsAcyclic

open Classical in
/-- SUBFOREST ISOMORPHISM as a decision problem over bitstrings. -/
noncomputable def subforestIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphIsomorphism.SubgraphIsomorphismFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SubforestIsomorphism
