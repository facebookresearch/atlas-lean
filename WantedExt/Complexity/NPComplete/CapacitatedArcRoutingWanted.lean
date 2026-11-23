/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED ARC ROUTING is NP-complete

Source:
B. L. Golden and R. T. Wong, "Capacitated arc routing problems", Networks 11 (1981), 305-315,
doi:10.1002/net.3230110308 (introduces the problem and shows it NP-hard);
R. van Bevern, S. Hartung, A. Nichterlein, and M. Sorge, "Constant-factor approximations for
Capacitated Arc Routing without triangle inequality", Operations Research Letters 42 (2014),
290-292, doi:10.1016/j.orl.2014.05.002, arXiv:1404.3660 (the problem statement used here);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN (the special case with
unbounded capacity; J. K. Lenstra and A. H. G. Rinnooy Kan, Networks 6 (1976), 273-280).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedArcRouting

/-!
# CAPACITATED ARC ROUTING is NP-complete

INSTANCE: an undirected graph `G = (V, E)`, a vehicle depot vertex `v₀ ∈ V`, edge costs
`c(e) ≥ 0` and edge demands `d(e) ≥ 0` for every `e ∈ E`, a vehicle capacity `W`, and a bound
`B`. QUESTION: is there a collection of routes, each a closed walk in `G` through the depot
`v₀` (the route of one vehicle), and a serving assignment, such that each route serves a set
of edges on it of total demand at most `W`, each edge `e` with `d(e) > 0` is served by exactly
one route, and the total cost of the routes is at most `B`?

This is the decision version of the optimization problem of Golden and Wong, as stated by
van Bevern, Hartung, Nichterlein, and Sorge. A route may traverse an edge without serving it,
and may traverse an edge several times; its cost counts the cost of every traversal. Routes
are given as a family indexed by the vehicles `Fin m` (two vehicles may drive the same walk),
each a Mathlib `SimpleGraph.Walk v₀ v₀`. The serving assignment maps every edge to the vehicle
that serves it; an edge of demand `0` need not lie on that route and adds `0` to its load, so
only the edges with `d(e) > 0` are constrained, as in the source. Binary encoding of all
numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list (an entry `(u, v, c, d)` is
the edge `{u, v}` with cost `c` and demand `d`), the depot `v₀`, the capacity `W`, and the
bound `B`. -/
abbrev CapacitatedArcRoutingInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The endpoint pairs of the listed edges. -/
def endpoints (i : CapacitatedArcRoutingInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CapacitatedArcRoutingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The cost of an edge `s`: the cost recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeCost (i : CapacitatedArcRoutingInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2.1).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and the depot is a
vertex. -/
def WellFormed (i : CapacitatedArcRoutingInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ (e.2.1, e.1) ∉ endpoints i) ∧
    i.2.2.1 < i.1

/-- Some `m` routes `C k`, closed walks at the depot `v₀`, and a serving assignment `s` (edge
entry `e` is served by route `s e`) satisfy: every edge of positive demand lies on the route
serving it; the edges served by each route have total demand at most `W`; and the routes have
total cost at most `B`, counting every traversal of an edge. -/
def CapacitatedArcRoutingFeasible (i : CapacitatedArcRoutingInstance) : Prop :=
  ∃ v₀ : Fin i.1, (v₀ : ℕ) = i.2.2.1 ∧
    ∃ (m : ℕ) (C : Fin m → (Graph i).Walk v₀ v₀) (s : Fin i.2.1.length → Fin m),
      (∀ e, 0 < (i.2.1.get e).2.2.2 →
        s((i.2.1.get e).1, (i.2.1.get e).2.1) ∈ (C (s e)).edges.map (Sym2.map Fin.val)) ∧
      (∀ k, ∑ e ∈ Finset.univ.filter (fun e => s e = k), (i.2.1.get e).2.2.2 ≤ i.2.2.2.1) ∧
      ∑ k, ((C k).edges.map (edgeCost i)).sum ≤ i.2.2.2.2

open Classical in
/-- CAPACITATED ARC ROUTING as a decision problem over bitstrings. -/
noncomputable def capacitatedArcRoutingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacitatedArcRoutingInstance) x with
  | some i => decide (WellFormed i ∧ CapacitatedArcRoutingFeasible i)
  | none => false

/-- **CAPACITATED ARC ROUTING is NP-complete.** Source: Golden and Wong (1981); van Bevern,
Hartung, Nichterlein, and Sorge (2014); Garey and Johnson (1979), [ND27] (special case). -/
public theorem_wanted capacitatedArcRouting_npComplete :
    capacitatedArcRoutingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacitatedArcRoutingDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedArcRouting
