/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BANDWIDTH for trees of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (comment: remains
NP-complete for trees with no vertex degree exceeding 3);
M. R. Garey, R. L. Graham, D. S. Johnson and D. E. Knuth, "Complexity results for bandwidth
minimization", SIAM Journal on Applied Mathematics 34 (1978), 477-495, doi:10.1137/0134037.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import WantedExt.Complexity.NPComplete.BandwidthWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BandwidthTreesMaxDegreeThree

/-!
# BANDWIDTH for trees of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` that is a tree in which no vertex has degree exceeding `3`, and a
positive integer `K ≤ |V|`. QUESTION: is there a linear ordering of `V` with bandwidth `K` or
less, i.e., a one-to-one function `f : V → {1, 2, …, |V|}` such that, for all `{u, v} ∈ E`,
`|f(u) - f(v)| ≤ K`?

This is the restriction of BANDWIDTH ([GT40], `BandwidthWanted`) to trees of maximum degree at
most `3`, the class of Garey, Graham, Johnson and Knuth: "it is NP-complete to determine whether
or not there exists an ordering of the vertices such that the adjacency matrix has bandwidth `≤
k`, even when `G` is restricted to the class of free trees with all vertices of degree `≤ 3`".
The instance type and the question are the parent's (`Bandwidth.BandwidthInstance`,
`Bandwidth.BandwidthFeasible`: the ordering is a permutation of `0, …, n - 1`, a vertex's
position its index in it); `WellFormed` is the parent's plus the restriction. The tree is
Mathlib's `SimpleGraph.IsTree` and degrees are `SimpleGraph.degree`, on the graph of the edge
list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : Bandwidth.BandwidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is a
tree with every vertex of degree at most `3`, and `0 < K ≤ n`. -/
def WellFormed (i : Bandwidth.BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ (Graph i).IsTree ∧ (∀ v, (Graph i).degree v ≤ 3) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- BANDWIDTH for trees of maximum degree 3 as a decision problem over bitstrings. -/
noncomputable def bandwidthTreesMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Bandwidth.BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ Bandwidth.BandwidthFeasible i)
  | none => false

/-- **BANDWIDTH for trees of maximum degree 3 is NP-complete.** Source: Garey and Johnson
(1979), [GT40]; Garey, Graham, Johnson and Knuth (1978). -/
public theorem_wanted bandwidthTreesMaxDegreeThree_npComplete :
    bandwidthTreesMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bandwidthTreesMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.BandwidthTreesMaxDegreeThree
