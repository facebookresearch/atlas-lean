/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COVERAGE LOCATION ON A NETWORK is NP-complete

Source:
N. Megiddo, E. Zemel, and S. L. Hakimi, "The maximum coverage location problem", SIAM Journal
on Algebraic and Discrete Methods 4 (1983), 253-261, doi:10.1137/0604028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation

/-!
# MAXIMUM COVERAGE LOCATION ON A NETWORK is NP-complete

INSTANCE: a graph `G = (V, E)` with a length `d(e) ∈ ℤ₀⁺` for each edge `e ∈ E`, a customer at
each vertex `v` with a gain `w(v) ∈ ℤ₀⁺` and a positive rational threshold radius `r(v)`, a
number `p` of new facilities, and a target `W`. QUESTION: can `p` facilities be located at
points of `G` (a point is a vertex or a point on an edge, the edge regarded as a line segment of
length `d(e)`) so that the customers covered, those `v` at distance less than `r(v)` from some
facility, have total gain at least `W`?

This is the maximum coverage location problem of Megiddo, Zemel, and Hakimi (1983) in decision
form: the distance between points is the length of a shortest route along the edges, a customer
`v` switches to a new facility "located at a distance less than `r_v`" (their abstract; §2
defines the `r_v`-neighborhood of `v` as the points at distance less than `r_v`), facilities may
be located anywhere on `G`, including interior points of edges, and the objective is the total
gain of the covered customers. They note that the problem is NP-hard on general graphs, by
expressing MINIMUM DOMINATING SET with unit lengths, unit gains, `r_v = 1.5` and `W = |V|`, and
solve it in polynomial time on trees. Binary encoding of all numbers.

A point is a triple `(a, b, t)`: the vertex `a` when `a = b` and `t = 0`, or, when `{a, b} ∈ E`,
the point of that edge at distance `t ∈ [0, d({a, b})]` from `a` (real `t`, as on a segment). A
shortest route from a vertex `v` to the point `(a, b, t)` enters it from `a` or from `b`, so its
length is `min (δ(v, a) + t, δ(v, b) + d({a, b}) - t)`, where `δ(v, a)` is the least total length
of a `SimpleGraph.Walk` from `v` to `a`. `DistLT i v x r` states that this distance is less than
`r`, existentially over walks. At most `p` facilities are located: more facilities never cover
fewer customers, and a point written in two ways is counted twice, which is harmless. Megiddo
et al. (§2) show that the facilities can be restricted to a finite candidate set of `O(|E| |V|)`
points determined by the distances and radii, so a certificate of polynomial size exists.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. The radius `r(v)` is a pair
`(a, b)` of naturals with `a > 0` and `b > 0`, standing for `a / b`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry
`(u, v, l)` is the edge `{u, v}` of length `l`), the customers of the vertices in order (an
entry `(w, a, b)` is the gain `w` and the radius `a / b`), the number `p` of facilities, and the
target `W`. -/
abbrev MaximumCoverageLocationInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MaximumCoverageLocationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the length recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : MaximumCoverageLocationInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- The total length of a walk (the sum of the lengths of its edges). -/
def walkLength (i : MaximumCoverageLocationInstance) {u v : Fin i.1}
    (W : (Graph i).Walk u v) : ℕ :=
  (W.edges.map (edgeLength i)).sum

/-- The gain `w(v)` of the customer at vertex `v`. -/
def gain (i : MaximumCoverageLocationInstance) (v : Fin i.1) : ℕ :=
  (i.2.2.1.getD v (0, 0, 1)).1

/-- The threshold radius `r(v) = a / b` of the customer at vertex `v`. -/
noncomputable def radius (i : MaximumCoverageLocationInstance) (v : Fin i.1) : ℝ :=
  ((i.2.2.1.getD v (0, 0, 1)).2.1 : ℝ) / (i.2.2.1.getD v (0, 0, 1)).2.2

/-- `(a, b, t)` is a point of `G`: the vertex `a` (`a = b`, `t = 0`), or the point of the edge
`{a, b}` at distance `t` from `a`, with `0 ≤ t ≤ d({a, b})`. -/
def OnGraph (i : MaximumCoverageLocationInstance) (x : Fin i.1 × Fin i.1 × ℝ) : Prop :=
  (x.1 = x.2.1 ∧ x.2.2 = 0) ∨
    ((Graph i).Adj x.1 x.2.1 ∧ 0 ≤ x.2.2 ∧ x.2.2 ≤ edgeLength i s(x.1, x.2.1))

/-- The shortest-route distance from vertex `v` to the point `x = (a, b, t)` is less than `r`:
some walk reaches `a` with total length plus `t` less than `r`, or reaches `b` with total length
plus `d({a, b}) - t` less than `r`. -/
def DistLT (i : MaximumCoverageLocationInstance) (v : Fin i.1) (x : Fin i.1 × Fin i.1 × ℝ)
    (r : ℝ) : Prop :=
  (∃ W : (Graph i).Walk v x.1, (walkLength i W : ℝ) + x.2.2 < r) ∨
    ∃ W : (Graph i).Walk v x.2.1,
      (walkLength i W : ℝ) + ((edgeLength i s(x.1, x.2.1) : ℝ) - x.2.2) < r

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and there is one
customer per vertex, each with a radius `a / b` where `0 < a` and `0 < b`. -/
def WellFormed (i : MaximumCoverageLocationInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    i.2.2.1.length = i.1 ∧ ∀ c ∈ i.2.2.1, 0 < c.2.1 ∧ 0 < c.2.2

open Classical in
/-- Some set `P` of at most `p` points of `G` covers customers of total gain at least `W`, a
customer `v` being covered when some point of `P` is at distance less than `r(v)` from `v`. -/
def MaximumCoverageLocationFeasible (i : MaximumCoverageLocationInstance) : Prop :=
  ∃ P : Finset (Fin i.1 × Fin i.1 × ℝ), P.card ≤ i.2.2.2.1 ∧ (∀ x ∈ P, OnGraph i x) ∧
    i.2.2.2.2 ≤ ∑ v with ∃ x ∈ P, DistLT i v x (radius i v), gain i v

open Classical in
/-- MAXIMUM COVERAGE LOCATION ON A NETWORK as a decision problem over bitstrings. -/
noncomputable def maximumCoverageLocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumCoverageLocationInstance) x with
  | some i => decide (WellFormed i ∧ MaximumCoverageLocationFeasible i)
  | none => false

/-- **MAXIMUM COVERAGE LOCATION ON A NETWORK is NP-complete.** Source: Megiddo, Zemel, and
Hakimi (1983). -/
public theorem_wanted maximumCoverageLocation_npComplete :
    maximumCoverageLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCoverageLocationDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation
