/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FAULT DETECTION WITH TEST POINTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS19] FAULT DETECTION WITH TEST POINTS
(p. 284), credited there to [Ibaraki, Kameda, and Toida, 1977], "NP-complete diagnosis problems
on systems graphs", listed in the book's bibliography as an unpublished manuscript
(transformation from X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FaultDetectionWithTestPointsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FaultDetectionWithTestPoints

/-!
# FAULT DETECTION WITH TEST POINTS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` having exactly one vertex `s ∈ V` with in-degree
`0` and exactly one vertex `t ∈ V` with out-degree `0`, and a positive integer `K`. QUESTION:
can all "single faults" in `G` be located by attaching `K` or fewer "test points" to arcs in
`A`, i.e., is there a subset `A' ⊆ A` with `|A'| ≤ K` such that the test set
`T = ({s} ∪ {u₁ : (u₁, u₂) ∈ A'}) × ({t} ∪ {u₂ : (u₁, u₂) ∈ A'})` has the property that, for each
pair `v, v' ∈ V - {s, t}`, there is some `(u₁, u₂) ∈ T` such that `v` is on a directed path from
`u₁` to `u₂` but `v'` is on no such path?

The directed graph is Mathlib's `Digraph`. The vertices `s` and `t` are determined by `G`; the
instance lists them, and `WellFormed` checks that they are the unique vertex of in-degree `0` and
the unique vertex of out-degree `0`. A vertex `v` lies on a directed path from `u₁` to `u₂`
exactly when `u₁` reaches `v` and `v` reaches `u₂` (reachability is the reflexive-transitive
closure of the arc relation, so a path may have length zero; in an acyclic graph every walk is
a path). The condition is required for every ordered pair of distinct vertices `v ≠ v'` of
`V - {s, t}`, with the roles of `v` and `v'` as in the source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FAULT DETECTION WITH TEST POINTS is NP-complete.** Source: Garey and Johnson (1979),
[MS19] (Ibaraki, Kameda, and Toida, unpublished). -/
public theorem_wanted faultDetectionWithTestPoints_npComplete :
    faultDetectionWithTestPointsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L faultDetectionWithTestPointsDec

end MetaMathlibExt.Complexity.NPComplete.FaultDetectionWithTestPoints
