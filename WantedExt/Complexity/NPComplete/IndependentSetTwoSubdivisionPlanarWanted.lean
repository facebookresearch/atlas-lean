/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on 2-subdivision ∩ planar graphs is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanarWanted
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoSubdivisionPlanar

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)
open MinimumCutLinearArrangementTwoSubdivisionPlanar (IsTwoSubdivision)

/-!
# INDEPENDENT SET on 2-subdivision ∩ planar graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is planar and a 2-subdivision, and a positive integer
`K ≤ |V|`. A 2-subdivision of a graph `H` results from inserting two new vertices in every edge,
that is, from replacing each edge `uv` of `H` by a path `u x y v` with new vertices `x, y`; `G`
is a 2-subdivision if it is the 2-subdivision of some graph (ISGCI's class 2-subdivision).
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) on ISGCI's class 2-subdivision ∩ planar (gc_675). Poljak's
construction replaces every edge of a graph `H` with `m` edges by a path of three edges, i.e.
forms the 2-subdivision of `H`, and the independence number grows by exactly `m`. Applied to
planar graphs, on which INDEPENDENT SET remains NP-complete ([GT20] comment), it yields planar
2-subdivisions, since subdividing edges preserves planarity. ISGCI records the class as
NP-complete, from Poljak.

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and the class,
with the predicates of `MinimumCutLinearArrangementTwoSubdivisionPlanarWanted`: planarity is
MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem
this is planarity), and `IsTwoSubdivision G` says that `G` is isomorphic to the 2-subdivision of
a simple graph given by a simple edge list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **INDEPENDENT SET on 2-subdivision ∩ planar graphs is NP-complete.** Source: Poljak (1974);
Garey and Johnson (1979), [GT20], comment (planar graphs); ISGCI (gc_675). -/
public theorem_wanted independentSetTwoSubdivisionPlanar_npComplete :
    independentSetTwoSubdivisionPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetTwoSubdivisionPlanarDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoSubdivisionPlanar
