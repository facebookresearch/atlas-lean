/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CYCLIC BANDWIDTH is NP-complete

Source:
J. Y.-T. Leung, O. Vornberger and J. D. Witthoff, "On some variants of the bandwidth minimization
problem", SIAM Journal on Computing 13 (1984), 650-667, doi:10.1137/0213040 (abstract: "the
cycle-bandwidth problem which for a given graph G and positive integer k, asks if there is a
circular layout such that every pair of adjacent vertexes have a distance at most k ... We show
that the cycle-bandwidth problem is NP-complete for each fixed k ≥ 2");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the linear version).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BandwidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CyclicBandwidth

open Bandwidth (BandwidthInstance)

/-!
# CYCLIC BANDWIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there a circular layout of `G` with every two adjacent vertices at distance at most
`K`, i.e. a bijection `f : V → {0, …, |V| - 1}` with `min(|f(u) - f(v)|, |V| - |f(u) - f(v)|) ≤ K`
for every edge `{u, v}`?

The positions `0, …, |V| - 1` lie on a cycle, so the distance between positions `a` and `b` is
the shorter way around, `min(|a - b|, |V| - |a - b|)`. The instance type (vertex count, edge
list, bound), its simple-edge-list well-formedness and the layout encoding (a list that is a
permutation of `0, …, n - 1`, vertex `v` at position `perm.idxOf v`) are those of BANDWIDTH
(`BandwidthWanted`, Garey and Johnson's [GT40]); this module replaces the linear distance by the
circular one and adds the source's `0 < K ≤ |V|`. Leung, Vornberger and Witthoff prove the problem
NP-complete even for every fixed `K ≥ 2`. Membership in NP: the positions of the edge-incident
vertices are a certificate (the remaining vertices fill the free positions).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The distance between positions `a` and `b` on a cycle of `n > 0` positions `0, …, n - 1`, the
shorter way around. Positions are taken modulo `n`, so every pair of naturals denotes two cycle
positions; for `a, b < n` this is `min(|a - b|, n - |a - b|)`. -/
def cyclicDist (n a b : ℕ) : ℕ :=
  min (Nat.dist (a % n) (b % n)) (n - Nat.dist (a % n) (b % n))

/-- Well-formedness of an instance: a well-formed BANDWIDTH instance (simple edge list) with
`0 < K ≤ n`. -/
def WellFormed (i : BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- A circular layout in which the endpoints of every edge are at cyclic distance at most `K`. -/
def CyclicBandwidthFeasible (i : BandwidthInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ e ∈ i.2.1, cyclicDist i.1 (perm.idxOf e.1) (perm.idxOf e.2) ≤ i.2.2

open Classical in
/-- CYCLIC BANDWIDTH as a decision problem over bitstrings. -/
noncomputable def cyclicBandwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ CyclicBandwidthFeasible i)
  | none => false

/-- **CYCLIC BANDWIDTH is NP-complete.** Source: Leung, Vornberger and Witthoff (1984); Garey and
Johnson (1979), [GT40] (linear version). -/
public theorem_wanted cyclicBandwidth_npComplete :
    cyclicBandwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cyclicBandwidthDec

end MetaMathlibExt.Complexity.NPComplete.CyclicBandwidth
