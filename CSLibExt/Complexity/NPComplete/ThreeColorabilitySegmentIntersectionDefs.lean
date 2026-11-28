/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH 3-COLORABILITY of segment intersection graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY, comment:
"Also remains NP-complete for K = 3 if G is an intersection graph for straight line segments in
the plane [Ehrlich, Even, and Tarjan, 1976]";
G. Ehrlich, S. Even and R. E. Tarjan, "Intersection graphs of curves in the plane", Journal of
Combinatorial Theory, Series B 21(1) (1976), 8-20, doi:10.1016/0095-8956(76)90022-8;
P. Ossona de Mendez, "3-colorability and contacts of segments", Série du CAMS 171 (1999), 1-2,
HAL hal-00008547 (Theorem 1: NP-complete even for contact graphs of segments in 4 directions,
from the grid T-shape contact representation of planar graphs of H. de Fraysseix, P. Ossona de
Mendez and P. Rosenstiehl, "On triangle contact graphs", Combinatorics, Probability and Computing
3 (1994), 233-246, doi:10.1017/S0963548300001139).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SegmentIntersectionCliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilitySegmentIntersection

open SegmentIntersectionClique (Seg toPoint segPoints)

/-- An instance: the list of segments. -/
abbrev ThreeColorabilitySegmentIntersectionInstance := List Seg

/-- The intersection graph of the segments: `SegmentIntersectionClique.Graph`, whose bound
component (here `0`) does not affect the graph. -/
def Graph (i : ThreeColorabilitySegmentIntersectionInstance) : SimpleGraph (Fin i.length) :=
  SegmentIntersectionClique.Graph (i, 0)

/-- Well-formedness of an instance: every segment has distinct endpoints, and the segments are
pairwise distinct as point sets. -/
def WellFormed (i : ThreeColorabilitySegmentIntersectionInstance) : Prop :=
  (∀ σ ∈ i, toPoint σ.1 ≠ toPoint σ.2) ∧ (i.map segPoints).Nodup

/-- The intersection graph of the segments is `3`-colorable. -/
def ThreeColorabilitySegmentIntersectionFeasible
    (i : ThreeColorabilitySegmentIntersectionInstance) : Prop :=
  (Graph i).Colorable 3

open Classical in
/-- GRAPH 3-COLORABILITY of segment intersection graphs as a decision problem over bitstrings. -/
noncomputable def threeColorabilitySegmentIntersectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeColorabilitySegmentIntersectionInstance) x with
  | some i => decide (WellFormed i ∧ ThreeColorabilitySegmentIntersectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilitySegmentIntersection
