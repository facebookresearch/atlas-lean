/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM SUBFOREST: definitions

Source:
R. Shamir and D. Tsur, "The maximum subforest problem: approximation and exact algorithms",
Proceedings of the Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 1998), 394-399,
doi:10.5555/314613.314769 (Section 1: the maximum subforest problem MSP; Section 1.1: "We show
that MSP is NP-hard");
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MAXIMUM
SUBFOREST;
A. Abboud, A. Backurs, T. D. Hansen, V. Vassilevska Williams and O. Zamir, "Subtree isomorphism
revisited", ACM Transactions on Algorithms 14(3) (2018), 1-23, doi:10.1145/3093239 (subtree
isomorphism, used for membership in NP).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumSubforest

open InducedSubgraphWithPropertyPi (SimpleEdgeList)

/-- An instance: the vertex count `n` and edge list of the tree `G`, the trees of `H` (each a
vertex count and an edge list), and the bound `K`. -/
abbrev MaximumSubforestInstance :=
  ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ)) × ℕ

/-- Well-formedness of an instance: `G` and every tree of `H` are simple graphs that are trees,
and `0 < K`. -/
def WellFormed (i : MaximumSubforestInstance) : Prop :=
  SimpleEdgeList i.1 i.2.1 ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsTree ∧
    (∀ T ∈ i.2.2.1, SimpleEdgeList T.1 T.2 ∧ (Cslib.Complexity.Karp.edgeGraph T.1 T.2).IsTree) ∧
    0 < i.2.2.2

/-- Some sublist `E'` of the edge list of `G`, of length at least `K`, spans a subgraph
`(V, E')` containing no copy of a tree of `H`. The length counts list entries, so it is an edge
count only for a simple edge list, which well-formedness checks. -/
def MaximumSubforestFeasible (i : MaximumSubforestInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ), E'.Sublist i.2.1 ∧ i.2.2.2 ≤ E'.length ∧
    ∀ T ∈ i.2.2.1,
      (Cslib.Complexity.Karp.edgeGraph T.1 T.2).Free (Cslib.Complexity.Karp.edgeGraph i.1 E')

open Classical in
/-- MAXIMUM SUBFOREST as a decision problem over bitstrings. -/
noncomputable def maximumSubforestDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumSubforestInstance) x with
  | some i => decide (WellFormed i ∧ MaximumSubforestFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumSubforest
