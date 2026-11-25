/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX MIN-MAX MULTICENTER (centers at vertices) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER, comment
(p. 220): "Variant in which we must choose a subset `P ⊆ V` is also NP-complete but solvable for
fixed `K` and for trees [Slater, 1976]";
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinMaxMulticenterWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexMinMaxMulticenter

open MinMaxMulticenter (MinMaxMulticenterInstance Graph walkLength weight)

/-!
# VERTEX MIN-MAX MULTICENTER (centers at vertices) is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(v) ∈ ℤ₀⁺` for each `v ∈ V`, a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a positive integer `K ≤ |V|`, and a positive rational `B`.
QUESTION: is there a set `P ⊆ V` of `K` vertices such that, if `d(v)` is the length of the
shortest path from `v` to the closest vertex in `P`, then `max {d(v) · w(v) : v ∈ V} ≤ B`?

This is the variant of [ND50] MIN-MAX MULTICENTER
(`WantedExt.Complexity.NPComplete.MinMaxMulticenterWanted`) in which the centers must be
vertices: the vertex-weighted vertex `p`-center problem, which Kariv and Hakimi prove NP-hard
(for vertex-weighted and vertex-unweighted networks, even on planar graphs of maximum degree 3).
The instance type, `Graph`, `walkLength` (the total length of a `SimpleGraph.Walk`), `weight`
and `MinMaxMulticenter.WellFormed` (simple edge list, one weight per vertex, `0 < K ≤ |V|`,
`B = p / q` with `p, q > 0`) are reused unchanged from the parent, and the parent's two disclosed
conventions carry over. `P`
has at most `K` vertices: adding centers never increases any `d(v)`, and `K ≤ |V|` vertices are
available, so "at most `K`" and "exactly `K`" agree. `d(v)` is defined only when some path joins
`v` to `P`, so every vertex must reach a vertex of `P`, whatever its weight. Since
`d(v) = min_{p ∈ P} min_W len(W)` over walks `W` from `v` to `p`, and `w(v) ≥ 0`, the question
reads: every vertex `v` has a center `p ∈ P` and a walk `W` from `v` to `p` with
`w(v) · len(W) ≤ B`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. The rational `B` is a pair
`(p, q)` of naturals with `q > 0`, standing for `p / q`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some set `P` of at most `K` vertices has, for every vertex `v`, a center `p ∈ P` and a walk
from `v` to `p` of total length `len` with `w(v) · len ≤ B`. -/
def VertexMinMaxMulticenterFeasible (i : MinMaxMulticenterInstance) : Prop :=
  ∃ P : Finset (Fin i.1), P.card ≤ i.2.2.2.1 ∧
    ∀ v : Fin i.1, ∃ p ∈ P, ∃ W : (Graph i).Walk v p,
      (weight i v : ℝ) * walkLength i W ≤ (i.2.2.2.2.1 : ℝ) / i.2.2.2.2.2

open Classical in
/-- VERTEX MIN-MAX MULTICENTER as a decision problem over bitstrings. -/
noncomputable def vertexMinMaxMulticenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinMaxMulticenterInstance) x with
  | some i => decide (MinMaxMulticenter.WellFormed i ∧ VertexMinMaxMulticenterFeasible i)
  | none => false

/-- **VERTEX MIN-MAX MULTICENTER (centers at vertices) is NP-complete.** Source: Garey and
Johnson (1979), [ND50], comment (Slater, 1976); Kariv and Hakimi (1979). -/
public theorem_wanted vertexMinMaxMulticenter_npComplete :
    vertexMinMaxMulticenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L vertexMinMaxMulticenterDec

end MetaMathlibExt.Complexity.NPComplete.VertexMinMaxMulticenter
