/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN SPLIT GRAPHS: definitions

Source:
K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly chordal
graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109;
recorded in M. Illuri, P. Renjith and N. Sadagopan, "Complexity of Steiner tree in split graphs -
dichotomy results", arXiv:1511.01668 (2016), abstract.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeSplitGraphs

open MetaMathlibExt.Complexity.NPComplete.SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- `G` is a split graph: some set of vertices is a clique and its complement is an independent
set. -/
def IsSplitGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S : Set V, G.IsClique S ∧ G.IsIndepSet Sᶜ

/-- Well-formedness of an instance: it is a well-formed STEINER TREE IN GRAPHS instance, every
edge has weight `1`, and its graph is a connected split graph. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).Connected ∧ IsSplitGraph (SteinerTree.Graph i i.2.1)

open Classical in
/-- STEINER TREE IN SPLIT GRAPHS as a decision problem over bitstrings. -/
noncomputable def steinerTreeSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeSplitGraphs
