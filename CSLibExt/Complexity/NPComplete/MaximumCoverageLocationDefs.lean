/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COVERAGE LOCATION ON A NETWORK: definitions

Source:
N. Megiddo, E. Zemel, and S. L. Hakimi, "The maximum coverage location problem", SIAM Journal
on Algebraic and Discrete Methods 4 (1983), 253-261, doi:10.1137/0604028.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation

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

end MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation
