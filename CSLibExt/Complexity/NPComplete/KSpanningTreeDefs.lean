/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-SPANNING TREE: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MINIMUM K-SPANNING TREE;
R. Ravi, R. Sundaram, M. V. Marathe, D. J. Rosenkrantz, and S. S. Ravi, "Spanning trees -
short or small", SIAM Journal on Discrete Mathematics 9 (1996), 178-200,
doi:10.1137/S0895480194266331.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeDefs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KSpanningTree

open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints Graph weight)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < k ≤ |V|`,
and `0 < K`. -/
def WellFormed (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ endpoints i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i) ∧
    0 < i.2.2.1 ∧ i.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2

/-- Some subtree `T` of `G` has at least `k` nodes and weight at most `K`. -/
def KSpanningTreeFeasible (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  ∃ T : (Graph i).Subgraph, T.coe.IsTree ∧ i.2.2.1 ≤ T.verts.ncard ∧
    ∑ᶠ e ∈ T.edgeSet, weight i e ≤ i.2.2.2

open Classical in
/-- K-SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def kSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedDiameterSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ KSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KSpanningTree
