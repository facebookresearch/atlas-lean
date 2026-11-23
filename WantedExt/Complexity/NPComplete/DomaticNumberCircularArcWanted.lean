/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMATIC NUMBER of circular-arc graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT3] DOMATIC NUMBER;
M. A. Bonuccelli, "Dominating sets and domatic number of circular arc graphs", Discrete Applied
Mathematics 12 (1985), 203-213, doi:10.1016/0166-218X(85)90025-3;
A. Sprague, "NP-completeness of the domatic number problem on circular arc graphs", Proceedings
of the 37th Annual ACM Southeast Regional Conference (1999), doi:10.1145/306363.306416.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CircularArcColoringWanted
public import WantedExt.Complexity.NPComplete.DomaticNumberWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DomaticNumberCircularArc

open MetaMathlibExt.Complexity.NPComplete

/-!
# DOMATIC NUMBER of circular-arc graphs is NP-complete

INSTANCE: a circular-arc graph `G = (V, E)` (the intersection graph of a finite family of arcs
on a circle) and a positive integer `K ≤ |V|`. QUESTION: is the domatic number of `G` at least
`K`, i.e. can `V` be partitioned into `k ≥ K` disjoint sets `V₁, …, Vₖ` such that each `Vᵢ` is
a dominating set for `G`? This is DOMATIC NUMBER (Garey and Johnson, [GT3]) restricted to
circular-arc graphs. Bonuccelli (1985) states that it is NP-complete for circular-arc graphs
(and polynomial for proper circular-arc graphs); Sprague (1999) reports that Bonuccelli's
reduction, from coloring circular-arc graphs, is in error, and proves the NP-completeness anew.

The instance type, the graph, the simple-graph and `0 < K ≤ |V|` conditions, and the question
are those of `DomaticNumber` (`DomaticNumberWanted`); the restriction adds that `G` is a
circular-arc graph (`IsCircularArcGraph`). Arcs are as in `CircularArcColoring`: closed arcs
whose endpoints are among `L` points `0, …, L - 1` in clockwise order on the circle, the arc
`(a, b)` running clockwise from `a` to `b` (`CircularArcColoring.OnArc`); every finite family of
closed arcs can be put in this form without changing which arcs meet, by numbering the distinct
endpoints in clockwise order, and two such arcs meet exactly when they share one of the points.
The graph is given by its edges and is well formed only if some arc family represents it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is a circular-arc graph: for some `L`, the vertices carry closed arcs with endpoints
among the `L` points of the circle such that two distinct vertices are adjacent exactly when
their arcs meet. -/
def IsCircularArcGraph (i : DomaticNumber.DomaticNumberInstance) : Prop :=
  ∃ L : ℕ, ∃ arc : Fin i.1 → ℕ × ℕ, (∀ v, (arc v).1 < L ∧ (arc v).2 < L) ∧
    ∀ u v, u ≠ v → ((DomaticNumber.Graph i).Adj u v ↔
      ∃ p < L, CircularArcColoring.OnArc (arc u) p ∧ CircularArcColoring.OnArc (arc v) p)

/-- Well-formedness of an instance: well formed for DOMATIC NUMBER (a simple graph and
`0 < K ≤ |V|`), and the graph is a circular-arc graph. -/
def WellFormed (i : DomaticNumber.DomaticNumberInstance) : Prop :=
  DomaticNumber.WellFormed i ∧ IsCircularArcGraph i

open Classical in
/-- DOMATIC NUMBER of circular-arc graphs as a decision problem over bitstrings. -/
noncomputable def domaticNumberCircularArcDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DomaticNumber.DomaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ DomaticNumber.DomaticNumberFeasible i)
  | none => false

/-- **DOMATIC NUMBER of circular-arc graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT3]; Bonuccelli (1985); Sprague (1999). -/
public theorem_wanted domaticNumberCircularArc_npComplete :
    domaticNumberCircularArcDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L domaticNumberCircularArcDec

end MetaMathlibExt.Complexity.NPComplete.DomaticNumberCircularArc
