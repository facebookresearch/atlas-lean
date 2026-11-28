/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-SUM MULTICENTER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND51] MIN-SUM MULTICENTER;
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. II: The
p-medians", SIAM Journal on Applied Mathematics 37 (1979), 539-560, doi:10.1137/0137041.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry
`(u, v, l)` is the edge `{u, v}` of length `l`), the weights `w(v)` of the vertices in order,
the number of points `K`, and the bound `B = p / q` as `(p, q)`. -/
abbrev MinSumMulticenterInstance := ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ × (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinSumMulticenterInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the length recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : MinSumMulticenterInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- The total length of a walk (the sum of the lengths of its edges). -/
def walkLength (i : MinSumMulticenterInstance) {u v : Fin i.1} (W : (Graph i).Walk u v) : ℕ :=
  (W.edges.map (edgeLength i)).sum

/-- The weight `w(v)` of vertex `v`. -/
def weight (i : MinSumMulticenterInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- `(a, b, t)` is a point on `G`: the vertex `a` (`a = b`, `t = 0`), or the point of the edge
`{a, b}` at distance `t` from `a`, with `0 ≤ t ≤ l({a, b})`. -/
def OnGraph (i : MinSumMulticenterInstance) (p : Fin i.1 × Fin i.1 × ℝ) : Prop :=
  (p.1 = p.2.1 ∧ p.2.2 = 0) ∨
    ((Graph i).Adj p.1 p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ edgeLength i s(p.1, p.2.1))

/-- The shortest-path distance from vertex `v` to the point `p = (a, b, t)` is at most `r`: some
walk reaches `a` with total length plus `t` at most `r`, or reaches `b` with total length plus
`l({a, b}) - t` at most `r`. -/
def DistLE (i : MinSumMulticenterInstance) (v : Fin i.1) (p : Fin i.1 × Fin i.1 × ℝ)
    (r : ℝ) : Prop :=
  (∃ W : (Graph i).Walk v p.1, (walkLength i W : ℝ) + p.2.2 ≤ r) ∨
    ∃ W : (Graph i).Walk v p.2.1,
      (walkLength i W : ℝ) + ((edgeLength i s(p.1, p.2.1) : ℝ) - p.2.2) ≤ r

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one weight
per vertex, `0 < K ≤ n`, and `B = p / q` with `0 < p`, `0 < q`. -/
def WellFormed (i : MinSumMulticenterInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    i.2.2.1.length = i.1 ∧
    0 < i.2.2.2.1 ∧ i.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2.1 ∧ 0 < i.2.2.2.2.2

/-- Some set `P` of at most `K` points on `G` has `∑_v w(v) · d(v) ≤ B`, where `d(v)` is the
distance from `v` to its closest point in `P`, witnessed by bounds `r(v) ≥ d(v)`. -/
def MinSumMulticenterFeasible (i : MinSumMulticenterInstance) : Prop :=
  ∃ P : Finset (Fin i.1 × Fin i.1 × ℝ), P.card ≤ i.2.2.2.1 ∧ (∀ p ∈ P, OnGraph i p) ∧
    ∃ r : Fin i.1 → ℝ, (∀ v, ∃ p ∈ P, DistLE i v p (r v)) ∧
      ∑ v, (weight i v : ℝ) * r v ≤ (i.2.2.2.2.1 : ℝ) / i.2.2.2.2.2

open Classical in
/-- MIN-SUM MULTICENTER as a decision problem over bitstrings. -/
noncomputable def minSumMulticenterDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinSumMulticenterInstance) x with
  | some i => decide (WellFormed i ∧ MinSumMulticenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter
