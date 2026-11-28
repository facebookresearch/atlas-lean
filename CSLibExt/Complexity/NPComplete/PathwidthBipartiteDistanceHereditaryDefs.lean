/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF BIPARTITE DISTANCE-HEREDITARY GRAPHS: definitions

Source:
T. Kloks, H. Bodlaender, H. Müller and D. Kratsch, "Computing treewidth and minimum fill-in: all
you need are the minimal separators", Proc. 1st European Symposium on Algorithms (ESA '93),
Lecture Notes in Computer Science 726, Springer (1993), 260-271, doi:10.1007/3-540-57273-2_61
(the original was not available to us; the result and its attribution are recorded by
Wikipedia, "Pathwidth": determining whether the pathwidth is at most `k` "remains NP-complete when
`G` is restricted to ... bipartite distance-hereditary graphs", citing this paper; R. Mihai and
I. Todinca, "Pathwidth is NP-hard for weighted trees", FAW 2009, LNCS 5598, 181-195,
doi:10.1007/978-3-642-02270-8_20, also credit it with NP-hardness for distance-hereditary
graphs);
E. Howorka, "A characterization of distance-hereditary graphs", Quarterly Journal of
Mathematics 28 (1977), 417-420, doi:10.1093/qmath/28.4.417 (the graph class).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthBipartiteDistanceHereditary

open PathwidthChordalGraphs (PathwidthChordalGraphsInstance Graph IsPathDecomposition
  PathwidthChordalGraphsFeasible)

/-- `G` is distance-hereditary: every connected induced subgraph preserves distances. -/
def IsDistanceHereditary {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.induce S).Connected → ∀ u v : S, (G.induce S).dist u v = G.dist u v

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is bipartite
and distance-hereditary, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsBipartite ∧ IsDistanceHereditary (Graph i) ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF BIPARTITE DISTANCE-HEREDITARY GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthBipartiteDistanceHereditaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthBipartiteDistanceHereditary
