/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-MAX MULTICENTER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER;
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter

/-!
# MIN-MAX MULTICENTER is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(v) ∈ ℤ₀⁺` for each `v ∈ V`, a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a positive integer `K ≤ |V|`, and a positive rational `B`.
QUESTION: is there a set `P` of `K` "points on `G`" (a point on `G` is either a vertex in `V` or
a point on an edge `e ∈ E`, with `e` regarded as a line segment of length `l(e)`) such that, if
`d(v)` is the length of the shortest path from `v` to the closest point in `P`, then
`max {d(v) · w(v) : v ∈ V} ≤ B`?

This is the absolute (points on edges allowed), vertex-weighted p-center problem of Kariv and
Hakimi, in Garey and Johnson's decision form. Binary encoding of all numbers.

A point is a triple `(a, b, t)`: the vertex `a` when `a = b` and `t = 0`, or, when `{a, b} ∈ E`,
the point of that edge at distance `t ∈ [0, l({a, b})]` from `a` (real `t`, as on a segment). A
shortest path from a vertex `v` to the point `(a, b, t)` enters it from `a` or from `b`, so
`d(v, (a, b, t)) = min (d(v, a) + t, d(v, b) + l({a, b}) - t)`, where `d(v, a)` is the least
total length of a `SimpleGraph.Walk` from `v` to `a`. `DistLE i v p r` states
`d(v, p) ≤ r` this way, existentially over walks. The question then reads: every vertex `v` has
a point `p ∈ P` and a bound `r ≥ d(v, p)` with `w(v) · r ≤ B`.

Two conventions are fixed and disclosed. `P` has at most `K` points: more points never increase
any `d(v)`, and `K ≤ |V|` vertices are available, so "at most `K`" and "exactly `K`" agree (and a
point written in two ways is counted twice, which is harmless). `G` is connected (in
`WellFormed`): `d(v)` is the length of a shortest path, so the source presupposes that a path
exists; on a disconnected graph `d(v)` would be infinite and `d(v) · w(v)` with `w(v) = 0`
would depend on a convention.

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

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry
`(u, v, l)` is the edge `{u, v}` of length `l`), the weights `w(v)` of the vertices in order,
the number of points `K`, and the bound `B = p / q` as `(p, q)`. -/
abbrev MinMaxMulticenterInstance := ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ × (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinMaxMulticenterInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the length recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : MinMaxMulticenterInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- The total length of a walk (the sum of the lengths of its edges). -/
def walkLength (i : MinMaxMulticenterInstance) {u v : Fin i.1} (W : (Graph i).Walk u v) : ℕ :=
  (W.edges.map (edgeLength i)).sum

/-- The weight `w(v)` of vertex `v`. -/
def weight (i : MinMaxMulticenterInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- `(a, b, t)` is a point on `G`: the vertex `a` (`a = b`, `t = 0`), or the point of the edge
`{a, b}` at distance `t` from `a`, with `0 ≤ t ≤ l({a, b})`. -/
def OnGraph (i : MinMaxMulticenterInstance) (p : Fin i.1 × Fin i.1 × ℝ) : Prop :=
  (p.1 = p.2.1 ∧ p.2.2 = 0) ∨
    ((Graph i).Adj p.1 p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ edgeLength i s(p.1, p.2.1))

/-- The shortest-path distance from vertex `v` to the point `p = (a, b, t)` is at most `r`: some
walk reaches `a` with total length plus `t` at most `r`, or reaches `b` with total length plus
`l({a, b}) - t` at most `r`. -/
def DistLE (i : MinMaxMulticenterInstance) (v : Fin i.1) (p : Fin i.1 × Fin i.1 × ℝ)
    (r : ℝ) : Prop :=
  (∃ W : (Graph i).Walk v p.1, (walkLength i W : ℝ) + p.2.2 ≤ r) ∨
    ∃ W : (Graph i).Walk v p.2.1,
      (walkLength i W : ℝ) + ((edgeLength i s(p.1, p.2.1) : ℝ) - p.2.2) ≤ r

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
connected, there is one weight per vertex, `0 < K ≤ n`, and `B = p / q` with `0 < p`, `0 < q`. -/
def WellFormed (i : MinMaxMulticenterInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (Graph i).Connected ∧ i.2.2.1.length = i.1 ∧
    0 < i.2.2.2.1 ∧ i.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2.1 ∧ 0 < i.2.2.2.2.2

/-- Some set `P` of at most `K` points on `G` has `w(v) · d(v) ≤ B` for every vertex `v`, where
`d(v)` is the distance from `v` to its closest point in `P`. -/
def MinMaxMulticenterFeasible (i : MinMaxMulticenterInstance) : Prop :=
  ∃ P : Finset (Fin i.1 × Fin i.1 × ℝ), P.card ≤ i.2.2.2.1 ∧ (∀ p ∈ P, OnGraph i p) ∧
    ∀ v : Fin i.1, ∃ p ∈ P, ∃ r : ℝ, DistLE i v p r ∧
      (weight i v : ℝ) * r ≤ (i.2.2.2.2.1 : ℝ) / i.2.2.2.2.2

open Classical in
/-- MIN-MAX MULTICENTER as a decision problem over bitstrings. -/
noncomputable def minMaxMulticenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinMaxMulticenterInstance) x with
  | some i => decide (WellFormed i ∧ MinMaxMulticenterFeasible i)
  | none => false

/-- **MIN-MAX MULTICENTER is NP-complete.** Source: Garey and Johnson (1979), [ND50]; Kariv and
Hakimi (1979). -/
public theorem_wanted minMaxMulticenter_npComplete :
    minMaxMulticenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minMaxMulticenterDec

end MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter
