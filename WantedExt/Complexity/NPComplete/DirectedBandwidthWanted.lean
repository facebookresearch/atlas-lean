/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED BANDWIDTH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT41] DIRECTED
BANDWIDTH;
M. R. Garey, R. L. Graham, D. S. Johnson, and D. E. Knuth, "Complexity results
for bandwidth minimization", SIAM Journal on Applied Mathematics 34 (1978),
477-495, doi:10.1137/0134037.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedBandwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedBandwidth

/-!
# DIRECTED BANDWIDTH is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` and a positive integer `K ≤ |V|`. QUESTION: is
there a one-to-one function `f : V → {1, 2, ..., |V|}` such that, for all `(u, v) ∈ A`,
`f(u) < f(v)` and `f(v) - f(u) ≤ K`?

The vertices are `0, ..., n - 1` and the arcs are given as a list of ordered pairs, with no
self-loops and no repeated arcs. Acyclicity is part of the instance class, so it is stated in
`WellFormed`: no vertex reaches itself along one or more arcs, that is, the transitive closure
(Mathlib's `Relation.TransGen`) of the arc relation is irreflexive. A one-to-one
`f : V → {1, ..., |V|}` is a bijection. As in `WantedExt.Complexity.NPComplete.BandwidthWanted`,
it is represented by a list `perm` that is a permutation of `0, ..., n - 1`: vertex `v` sits at
position `perm.idxOf v`, and `f(v) = perm.idxOf v + 1`. The shift by one changes neither
`f(u) < f(v)` nor `f(v) - f(u)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED BANDWIDTH is NP-complete.** Source: Garey and Johnson (1979), [GT41]; Garey,
Graham, Johnson, and Knuth (1978). -/
public theorem_wanted directedBandwidth_npComplete :
    directedBandwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedBandwidthDec

end MetaMathlibExt.Complexity.NPComplete.DirectedBandwidth
