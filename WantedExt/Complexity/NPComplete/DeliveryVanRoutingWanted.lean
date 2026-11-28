/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DELIVERY VAN ROUTING is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3, problem [4] DELIVERY VAN ROUTING (reference: H. Boers,
"The 'race graph': an NP-complete problem", manuscript, 1982, not available; transformation from
3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DeliveryVanRoutingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeliveryVanRouting

/-!
# DELIVERY VAN ROUTING is NP-complete

INSTANCE: a directed graph `G = (V, A)`, each arc `a` of which has an associated (possibly
negative) integer weight `w(a)`, and a vertex `s ∈ V`.
QUESTION: is there a permutation `P = (a₁, ..., a_m)` of the arcs in `A` such that (i) for all
`i`, `1 ≤ i < m`, the head of `aᵢ` coincides with the tail of `aᵢ₊₁` (i.e. `P` is an Euler tour
of `G`), (ii) `s` is the tail of `a₁` and the head of `a_m`, and (iii) for all `j`, `1 ≤ j ≤ m`,
`∑_{i=1}^{j} w(aᵢ) ≤ 0`?

Johnson reports the problem NP-complete (Boers, by a transformation from 3SAT), even when every
vertex has in-degree equal to out-degree and all weights are in `{-1, 1}`.

The vertices are `0, ..., n - 1`, and the arcs are a list of entries `(tail, head, w)` without
two arcs with the same tail and head and without loops (the convention of the directed graphs in
this directory, e.g. `FeedbackArcSetWanted`). A weight is an integer given as a (positive part,
negative part) pair, as in `ZeroOneILPWanted`; numbers use the binary encoding. The permutation
`P` is a list of arc indices that is a permutation of all of them. Condition (ii) refers to
`a₁`, so the tour is nonempty: an instance with no arcs is a no-instance. Condition (iii) is
stated for the prefixes of every length `j ≤ m` (the empty prefix has weight `0`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DELIVERY VAN ROUTING is NP-complete.** Source: Johnson (1982), NP-completeness column,
problem [4] (Boers). -/
public theorem_wanted deliveryVanRouting_npComplete :
    deliveryVanRoutingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L deliveryVanRoutingDec

end MetaMathlibExt.Complexity.NPComplete.DeliveryVanRouting
