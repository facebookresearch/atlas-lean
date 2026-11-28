/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on 2-subdivision ∩ planar graphs: definitions

Source:
S. Poljak, "A note on stable sets and colorings of graphs", Commentationes Mathematicae
Universitatis Carolinae 15 (1974), 307-309;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 195, problem [GT20] INDEPENDENT SET,
comment: "Remains NP-complete for cubic planar graphs";
ISGCI, *Information System on Graph Classes and their Inclusions*, class 2-subdivision ∩ planar
(gc_675, https://www.graphclasses.org/classes/gc_675.html), problem Independent set:
NP-complete, from Poljak.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanarDefs
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoSubdivisionPlanar

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)
open MinimumCutLinearArrangementTwoSubdivisionPlanar (IsTwoSubdivision)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is a
2-subdivision and planar, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsTwoSubdivision (Graph i) ∧ (Graph i).IsPlanar ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on 2-subdivision ∩ planar graphs as a decision problem over bitstrings. -/
noncomputable def independentSetTwoSubdivisionPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoSubdivisionPlanar
