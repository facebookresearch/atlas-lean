/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED CONNECTED SUBGRAPH WITH PROPERTY Π: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT22] INDUCED CONNECTED SUBGRAPH
WITH PROPERTY Π;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proc. 10th ACM Symposium on
Theory of Computing (STOC 1978), 253-264, doi:10.1145/800133.804355;
M. Yannakakis, "The effect of a connectivity requirement on the complexity of maximum subgraph
problems", Journal of the ACM 26 (1979), 618-630, doi:10.1145/322154.322157.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import CSLibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPiDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedConnectedSubgraphWithPropertyPi

open MetaMathlibExt.Complexity.NPComplete.InducedSubgraphWithPropertyPi

/-- `Φ` holds for arbitrarily large connected graphs but not for all connected graphs. -/
def IsConnectedNontrivial (Φ : GraphProperty) : Prop :=
  (∀ m, ∃ n, m ≤ n ∧ ∃ G : SimpleGraph (Fin n), G.Connected ∧ Φ n G) ∧
    ∃ n, ∃ G : SimpleGraph (Fin n), G.Connected ∧ ¬ Φ n G

/-- Some set of at least `K` vertices induces a connected subgraph with property `Φ`: for some
`m ≥ K` and some injective `f : Fin m ↪ Fin n`, the subgraph induced by the range of `f` is
connected and has `Φ`. -/
def InducedConnectedSubgraphWithPropertyPiFeasible (Φ : GraphProperty)
    (i : InducedSubgraphWithPropertyPiInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ ∃ f : Fin m ↪ Fin i.1,
    ((Graph i).comap f).Connected ∧ Φ m ((Graph i).comap f)

open Classical in
/-- INDUCED CONNECTED SUBGRAPH WITH PROPERTY `Φ` as a decision problem over bitstrings. -/
noncomputable def inducedConnectedSubgraphWithPropertyPiDec (Φ : GraphProperty) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedSubgraphWithPropertyPiInstance) x with
  | some i => decide (WellFormed i ∧ InducedConnectedSubgraphWithPropertyPiFeasible Φ i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InducedConnectedSubgraphWithPropertyPi
