/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# DISCRETE (r|X_p)-MEDIANOID: definitions

The follower's problem of competitive location on a network, Hakimi's `(r|X_p)`-medianoid,
in its discrete form (new facilities at vertices). An instance is a graph with positive integer
edge lengths and nonnegative integer vertex weights (the customers' demand, located at the
vertices), a set `X_p` of vertices holding the competitor's existing facilities, an integer
`r` and a target `W`. A customer patronizes the follower only if a new facility is strictly
closer to it than every existing facility (shortest-path distance). The question is whether
`r` new facilities can be placed at vertices so that the total weight of the customers they
capture is at least `W`. All numbers are in binary encoding.

Lazar and Tamir (2013) record that Hakimi proved the absolute and the discrete
`(r|X)`-medianoid problems strongly NP-hard on general graphs, even when `X` is a single
vertex. NP membership is immediate (shortest-path distances are polynomial-time computable).

The `r` new facilities occupy `r` distinct vertices (a facility at a competitor's vertex
captures nothing there, as distance `0` is not strictly smaller). The graph need not be
connected: a vertex with no path to `X_p` is captured by a new facility it can reach, as its
distance to `X_p` is infinite; connected instances, which the source considers, are a special
case.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
S. L. Hakimi, "On locating new facilities in a competitive environment", European Journal of
Operational Research 12 (1983), 29-35, doi:10.1016/0377-2217(83)90180-7;
A. Lazar and A. Tamir, "Improved algorithms for some competitive location centroid problems
on paths, trees and graphs", Algorithmica 66 (2013), 615-640, doi:10.1007/s00453-012-9655-1.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CompetitiveLocationMedianoid

/-- An instance: vertex count `n`, edges as `(u, v, length)`, vertex weights (indexed by
vertex), the existing facilities `X_p` (vertices), the number `r` of new facilities and the
target `W`. -/
abbrev CompetitiveLocationMedianoidInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × List ℕ × List ℕ × ℕ × ℕ

/-- The endpoint pairs of the edge list. -/
def endpoints (i : CompetitiveLocationMedianoidInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CompetitiveLocationMedianoidInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The length of an edge (the length of the first list entry with these endpoints; in a
well-formed instance there is exactly one). -/
def edgeLength (i : CompetitiveLocationMedianoidInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- The length of a walk: the sum of the lengths of its edges. -/
def walkLength (i : CompetitiveLocationMedianoidInstance) {u v : Fin i.1}
    (p : (Graph i).Walk u v) : ℕ :=
  (p.edges.map (edgeLength i)).sum

/-- The weight of vertex `v`. -/
def weight (i : CompetitiveLocationMedianoidInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no loops, no repeated or
reversed edges) with positive lengths, one weight per vertex, and existing facilities at
vertices. -/
def WellFormed (i : CompetitiveLocationMedianoidInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ (e.2.1, e.1) ∉ endpoints i ∧
      0 < e.2.2) ∧
    i.2.2.1.length = i.1 ∧ ∀ x ∈ i.2.2.2.1, x < i.1

/-- The customer at `v` patronizes a new facility of `Y`: some walk from `v` to a vertex of
`Y` is strictly shorter than every walk from `v` to an existing facility. -/
def Captured (i : CompetitiveLocationMedianoidInstance) (Y : Finset (Fin i.1)) (v : Fin i.1) :
    Prop :=
  ∃ y ∈ Y, ∃ p : (Graph i).Walk v y,
    ∀ x : Fin i.1, (x : ℕ) ∈ i.2.2.2.1 → ∀ q : (Graph i).Walk v x, walkLength i p < walkLength i q

open Classical in
/-- `r` new facilities at distinct vertices capture customers of total weight at least `W`. -/
def CompetitiveLocationMedianoidFeasible (i : CompetitiveLocationMedianoidInstance) : Prop :=
  ∃ Y : Finset (Fin i.1), Y.card = i.2.2.2.2.1 ∧
    i.2.2.2.2.2 ≤ ∑ v ∈ Finset.univ.filter (Captured i Y), weight i v

open Classical in
/-- DISCRETE (r|X_p)-MEDIANOID as a decision problem over bitstrings. -/
noncomputable def competitiveLocationMedianoidDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CompetitiveLocationMedianoidInstance) x with
  | some i => decide (WellFormed i ∧ CompetitiveLocationMedianoidFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CompetitiveLocationMedianoid
