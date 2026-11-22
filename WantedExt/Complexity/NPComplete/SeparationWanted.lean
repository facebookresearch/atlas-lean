/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEPARATION is NP-complete

Source:
J. Y.-T. Leung, O. Vornberger and J. D. Witthoff, "On some variants of the bandwidth minimization
problem", SIAM Journal on Computing 13 (1984), 650-667, doi:10.1137/0213040 (abstract: "the
separation problem which asks if there is a linear layout such that every pair of adjacent
vertexes have a distance greater than k ... the separation and cycle-separation problems are
both NP-complete for each fixed k ≥ 1"; the full text was not available to us);
Z. Miller and D. Pritikin, "On the separation number of a graph", Networks 19 (1989), 651-666,
doi:10.1002/net.3230190604 (restates the result: the problem "given a graph G and an integer k,
is the quantity defined above greater than k?" is NP-complete, even for the case k = 1, by a
simple reduction from the Hamiltonian path problem);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the dual problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BandwidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Separation

open Bandwidth (BandwidthInstance)

/-!
# SEPARATION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a linear layout of `G` in which every two adjacent vertices are at distance
greater than `K`, i.e. a bijection `f : V → {0, …, |V| - 1}` with `|f(u) - f(v)| > K` for every
edge `{u, v}`?

This is the dual of BANDWIDTH ([GT40]): the separation number of `G`, the largest
`min {|f(u) - f(v)| : uv ∈ E}` over all layouts `f` (Miller and Pritikin), exceeds `K`. The
instance type (vertex count, edge list, bound), its simple-edge-list well-formedness and the
layout encoding (a list that is a permutation of `0, …, n - 1`, vertex `v` at position
`perm.idxOf v`) are those of BANDWIDTH (`BandwidthWanted`); this module reverses the inequality
to `> K` and adds the source's `0 < K`. For `K = 1` a layout is a Hamiltonian path of the
complement of `G`. Membership in NP: the positions of the edge-incident vertices are a
certificate (the remaining vertices fill the free positions).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed BANDWIDTH instance (simple edge list) with
`0 < K`. -/
def WellFormed (i : BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ 0 < i.2.2

/-- A linear layout in which the endpoints of every edge are at distance greater than `K`. -/
def SeparationFeasible (i : BandwidthInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ e ∈ i.2.1, i.2.2 < Nat.dist (perm.idxOf e.1) (perm.idxOf e.2)

open Classical in
/-- SEPARATION as a decision problem over bitstrings. -/
noncomputable def separationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ SeparationFeasible i)
  | none => false

/-- **SEPARATION is NP-complete.** Source: Leung, Vornberger and Witthoff (1984); Miller and
Pritikin (1989); Garey and Johnson (1979), [GT40] (the dual problem). -/
public theorem_wanted separation_npComplete :
    separationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L separationDec

end MetaMathlibExt.Complexity.NPComplete.Separation
