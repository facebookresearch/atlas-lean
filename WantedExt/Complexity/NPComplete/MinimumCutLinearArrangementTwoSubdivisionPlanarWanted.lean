/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar 2-subdivision graphs is NP-complete

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58(1-3) (1988), 209-229, doi:10.1016/0304-3975(88)90028-X (Min Cut is
NP-complete for planar graphs with maximum vertex degree 3);
ISGCI, Information System on Graph Classes and their Inclusions, class 2-subdivision ∩ planar
(gc_675, https://www.graphclasses.org/classes/gc_675.html), problem cutwidth decomposition, and
its note on 2-subdivision graphs (reference 1648: homeomorphic graphs have the same cutwidth);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT44] MINIMUM CUT LINEAR ARRANGEMENT.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import WantedExt.Complexity.NPComplete.MinimumCutLinearArrangementWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanar

open MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangement
  (MinimumCutLinearArrangementInstance MinimumCutLinearArrangementFeasible)

/-!
# MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar 2-subdivision graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is planar and a 2-subdivision, and a positive integer `K`.
A 2-subdivision of a graph `H` results from inserting two new vertices in every edge, that is,
from replacing each edge `uv` of `H` by a path `u x y v` with new vertices `x, y`; `G` is a
2-subdivision if it is the 2-subdivision of some graph (ISGCI's class 2-subdivision, gc_472).
QUESTION: is the cutwidth of `G` at most `K`, i.e. is there a one-to-one function
`f : V → {1, 2, ..., |V|}` such that for all `i`, `1 ≤ i < |V|`,
`|{{u, v} ∈ E : f(u) ≤ i < f(v)}| ≤ K`?

This is the restriction of MINIMUM CUT LINEAR ARRANGEMENT ([GT44],
`MinimumCutLinearArrangementWanted`) to ISGCI's class 2-subdivision ∩ planar (gc_675). The
instance type and the question are the parent's
(`MinimumCutLinearArrangement.MinimumCutLinearArrangementInstance`,
`MinimumCutLinearArrangement.MinimumCutLinearArrangementFeasible`), and `WellFormed` is the
parent's (a simple edge list on `0, ..., n - 1` and `0 < K`) plus the restriction, on the
instance's graph `Cslib.Complexity.Karp.edgeGraph`:

* planarity is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by
  Fáry's theorem this is planarity);
* `IsTwoSubdivision`: `G` is isomorphic (Mathlib's `SimpleGraph.Iso`) to the 2-subdivision of a
  simple graph `H` on `0, ..., m - 1` given by a simple edge list `es`. The 2-subdivision has the
  vertices `0, ..., m + 2 |es| - 1`, and its edges (`twoSubdivisionEdges`) replace the `j`-th
  edge `(a, b)` of `es` by the path `a - (m + 2j) - (m + 2j + 1) - b`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The edges of the 2-subdivision of the graph on `0, ..., m - 1` with edge list `es`: the
`j`-th edge `(a, b)` becomes the path `a - (m + 2j) - (m + 2j + 1) - b` through two new
vertices. -/
def twoSubdivisionEdges (m : ℕ) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.zipIdx.flatMap fun (e, j) =>
    [(e.1, m + 2 * j), (m + 2 * j, m + 2 * j + 1), (m + 2 * j + 1, e.2)]

/-- `G` is a 2-subdivision: it is isomorphic to the 2-subdivision of a simple graph on
`0, ..., m - 1` with a simple edge list `es` (no duplicate edges in either orientation, no
self-loops, endpoints in range). -/
def IsTwoSubdivision {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (m : ℕ) (es : List (ℕ × ℕ)),
    (es.Nodup ∧ ∀ e ∈ es, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ es) ∧
      Nonempty (G ≃g Cslib.Complexity.Karp.edgeGraph (m + 2 * es.length)
        (twoSubdivisionEdges m es))

/-- Well-formedness of an instance: the parent's (the edge list describes a simple graph on
`0, ..., n - 1`, and `0 < K`), and the graph is a 2-subdivision and planar. -/
def WellFormed (i : MinimumCutLinearArrangementInstance) : Prop :=
  MinimumCutLinearArrangement.WellFormed i ∧
    IsTwoSubdivision (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
      (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsPlanar

open Classical in
/-- MINIMUM CUT LINEAR ARRANGEMENT for planar 2-subdivision graphs as a decision problem over
bitstrings. -/
noncomputable def minimumCutLinearArrangementTwoSubdivisionPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumCutLinearArrangementInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCutLinearArrangementFeasible i)
  | none => false

/-- **MINIMUM CUT LINEAR ARRANGEMENT (CUTWIDTH) for planar 2-subdivision graphs is
NP-complete.** Source: Monien and Sudborough (1988); ISGCI (gc_675); Garey and Johnson (1979),
[GT44]. -/
public theorem_wanted minimumCutLinearArrangementTwoSubdivisionPlanar_npComplete :
    minimumCutLinearArrangementTwoSubdivisionPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCutLinearArrangementTwoSubdivisionPlanarDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCutLinearArrangementTwoSubdivisionPlanar
