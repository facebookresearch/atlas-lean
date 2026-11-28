/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF DISTANCE-HEREDITARY GRAPHS: definitions

Source:
T. Kloks, H. L. Bodlaender, H. Müller, and D. Kratsch, "Computing treewidth and minimum fill-in:
all you need are the minimal separators", Algorithms - ESA '93, Lecture Notes in Computer Science
726 (1993), 260-271, doi:10.1007/3-540-57273-2_61 (pathwidth is NP-complete on bipartite
distance-hereditary graphs);
I. Adler, M. M. Kanté, and O. Kwon, "Linear rank-width of distance-hereditary graphs I. A
polynomial-time algorithm", Algorithmica 78 (2017), 342-377, doi:10.1007/s00453-016-0164-5,
arXiv:1403.1081 (records that computing the pathwidth of distance-hereditary graphs is NP-hard);
E. Howorka, "A characterization of distance-hereditary graphs", The Quarterly Journal of
Mathematics 28 (1977), 417-420, doi:10.1093/qmath/28.4.417 (the definition).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthDistanceHereditaryGraphs

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph PathwidthChordalGraphsFeasible)

/-- `G` is distance-hereditary: every connected induced subgraph `G[S]` preserves distances. -/
def IsDistanceHereditary {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Set (Fin n), (G.induce S).Connected → ∀ u v : S, (G.induce S).dist u v = G.dist u v

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
distance-hereditary, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsDistanceHereditary (Graph i) ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF DISTANCE-HEREDITARY GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthDistanceHereditaryGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthDistanceHereditaryGraphs
