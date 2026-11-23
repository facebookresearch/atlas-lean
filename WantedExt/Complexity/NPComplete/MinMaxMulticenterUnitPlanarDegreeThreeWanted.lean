/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-MAX MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3 is
NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER, p. 220
(comment: "Remains NP-complete if `w(v) = 1` for all `v ∈ V` and `l(e) = 1` for all `e ∈ E`"),
and problem [GT2] DOMINATING SET, p. 190 (comment: "Remains NP-complete for planar graphs with
maximum vertex degree 3");
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040;
A. Kolen, "Complexity of location problems on networks", Report BW 107/79, Mathematisch Centrum,
Amsterdam (1979), Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card
public import WantedExt.Complexity.NPComplete.MinMaxMulticenterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter
  (MinMaxMulticenterInstance Graph MinMaxMulticenterFeasible)

/-!
# MIN-MAX MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3 is
NP-complete

INSTANCE: a planar graph `G = (V, E)` in which no vertex has degree exceeding 3, weights
`w(v) = 1` for all `v ∈ V`, lengths `l(e) = 1` for all `e ∈ E`, a positive integer `K ≤ |V|`,
and a positive rational `B`.
QUESTION: is there a set `P` of `K` "points on `G`" (a point on `G` is either a vertex in `V` or
a point on an edge `e ∈ E`, with `e` regarded as a line segment of length `l(e)`) such that, if
`d(v)` is the length of the shortest path from `v` to the closest point in `P`, then
`max {d(v) · w(v) : v ∈ V} ≤ B`?

This is MIN-MAX MULTICENTER ([ND50], `MinMaxMulticenterWanted`) restricted to unit weights and
lengths, the restriction of the entry's comment, on planar graphs of maximum degree 3, the class
for which Kariv and Hakimi show that the (absolute or vertex) `p`-center problem stays NP-hard.
Kolen (Theorem 1) gives the reduction from DOMINATING SET that Garey and Johnson's comment
records: the same graph, unit weights and lengths, `K` points and `B = 1`. A dominating set of
size at most `K` gives `K` vertices within distance 1 of every vertex, and conversely moving each
point of `P` to the closest endpoint of its edge keeps every vertex within distance 1, which
gives a dominating set. The graph is unchanged, so DOMINATING SET on planar graphs of maximum
degree 3 ([GT2], comment) reduces to this restricted problem.

The instance type, `MinMaxMulticenter.WellFormed` (simple edge list, one weight per vertex,
`0 < K ≤ |V|`, `B = p / q` with `p, q > 0`) and `MinMaxMulticenter.MinMaxMulticenterFeasible`
(points on edges at real positions, with the parent's two disclosed conventions) are reused
unchanged. `WellFormed` adds the restriction: every weight is `1`, every edge length is `1`, the
graph is planar (the shared MathlibExt predicate `SimpleGraph.IsPlanar`, a crossing-free
straight-line drawing; by Fáry's theorem this is planarity for finite simple graphs), and every
vertex has at most 3 neighbours.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MIN-MAX MULTICENTER instance with all weights
`1` and all edge lengths `1`, whose graph is planar with maximum degree at most 3. -/
def WellFormed (i : MinMaxMulticenterInstance) : Prop :=
  MinMaxMulticenter.WellFormed i ∧ (∀ w ∈ i.2.2.1, w = 1) ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (Graph i).IsPlanar ∧ ∀ v : Fin i.1, ((Graph i).neighborSet v).ncard ≤ 3

open Classical in
/-- MIN-MAX MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3, as a
decision problem over bitstrings. -/
noncomputable def minMaxMulticenterUnitPlanarDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinMaxMulticenterInstance) x with
  | some i => decide (WellFormed i ∧ MinMaxMulticenterFeasible i)
  | none => false

/-- **MIN-MAX MULTICENTER is NP-complete with unit weights and lengths on planar graphs of
maximum degree 3.** Source: Garey and Johnson (1979), [ND50] and [GT2], comments; Kariv and
Hakimi (1979); Kolen (1979), Theorem 1. -/
public theorem_wanted minMaxMulticenterUnitPlanarDegreeThree_npComplete :
    minMaxMulticenterUnitPlanarDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minMaxMulticenterUnitPlanarDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThree
