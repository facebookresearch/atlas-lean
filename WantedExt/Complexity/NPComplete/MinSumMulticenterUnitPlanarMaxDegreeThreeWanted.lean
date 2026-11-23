/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-SUM MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND51] MIN-SUM MULTICENTER (p. 220),
comment "Remains NP-complete if w(v) = 1 for all v ∈ V and l(e) = 1 for all e ∈ E";
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. II: The
p-medians", SIAM Journal on Applied Mathematics 37 (1979), 539-560, doi:10.1137/0137041
(NP-hard "even when the network has a simple structure (e.g., planar graph of maximum vertex
degree 3)").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import WantedExt.Complexity.NPComplete.MinSumMulticenterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

/-!
# MIN-SUM MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3

INSTANCE: a planar graph `G = (V, E)` with maximum vertex degree at most `3`, the weight
`w(v) = 1` for each `v ∈ V`, the length `l(e) = 1` for each `e ∈ E`, a positive integer
`K ≤ |V|`, and a positive rational `B`. QUESTION: is there a set `P` of `K` "points on `G`"
such that, if `d(v)` is the length of the shortest path from `v` to the closest point in `P`,
then `∑_{v ∈ V} d(v) · w(v) ≤ B`?

This is the restriction of MIN-SUM MULTICENTER ([ND51], `MinSumMulticenterWanted`) to unit
weights and lengths ([ND51]'s comment) on planar graphs of maximum degree `3` (the class of
Kariv and Hakimi's hardness result). The instance type, `MinSumMulticenter.WellFormed`, the
points on `G`, the distances and `MinSumMulticenter.MinSumMulticenterFeasible` are the parent's,
unchanged, with its two disclosed conventions (at most `K` points; every vertex must reach a
point). `WellFormed` adds the weights and lengths, planarity as the repository's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for planar graphs), and the degree bound as Mathlib's `SimpleGraph.degree`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance: a well-formed MIN-SUM MULTICENTER instance in which every
vertex weight and every edge length is `1`, whose graph is planar with every vertex degree at
most `3`. -/
def WellFormed (i : MinSumMulticenterInstance) : Prop :=
  MinSumMulticenter.WellFormed i ∧ (∀ w ∈ i.2.2.1, w = 1) ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (Graph i).IsPlanar ∧ ∀ v, (Graph i).degree v ≤ 3

open Classical in
/-- MIN-SUM MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3 as
a decision problem over bitstrings. -/
noncomputable def minSumMulticenterUnitPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinSumMulticenterInstance) x with
  | some i => decide (WellFormed i ∧ MinSumMulticenterFeasible i)
  | none => false

/-- **MIN-SUM MULTICENTER is NP-complete with unit weights and lengths on planar graphs of
maximum degree 3.** Source: Garey and Johnson (1979), [ND51], comment; Kariv and Hakimi
(1979). -/
public theorem_wanted minSumMulticenterUnitPlanarMaxDegreeThree_npComplete :
    minSumMulticenterUnitPlanarMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minSumMulticenterUnitPlanarMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThree
