/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IDENTIFYING CODE is NP-complete

Source:
I. Charon, O. Hudry and A. Lobstein, "Minimizing the size of an identifying or locating-dominating
code in a graph is NP-hard", Theoretical Computer Science 290 (2003), 2109-2120,
doi:10.1016/S0304-3975(02)00536-4, Theorem 2.1 (with `r = 1`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IdentifyingCodeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IdentifyingCode

/-!
# IDENTIFYING CODE is NP-complete

INSTANCE: a connected graph `G = (V, E)` (finite, simple, undirected) and an integer
`K ≤ |V|`. QUESTION: is there an identifying code `C ⊆ V` of size at most `K`, that is, a set `C`
such that the sets `B₁(v) ∩ C`, `v ∈ V`, are all nonempty and pairwise different, where `B₁(v)`
is the ball of radius `1` around `v`?

Charon, Hudry and Lobstein (Section 1) define, for a finite, undirected, connected graph, the
ball `Bᵣ(v) = {x ∈ V : d(x, v) ≤ r}` and call a code `C` `r`-identifying when the sets
`Bᵣ(v) ∩ C` are all nonempty and different; their Theorem 2.1 states that for every `r ≥ 1` the
decision problem "INSTANCE: a connected graph `G = (V, E)` and an integer `k ≤ |V|`; QUESTION: is
there an `r`-identifying code `C ⊆ V` of size at most `k`?" is NP-complete. This module states the
case `r = 1`, the identifying codes of the record.

The graph is given by its vertex count and a simple edge list (`Cslib.Complexity.Karp.edgeGraph`),
and `d` is Mathlib's `SimpleGraph.dist`. Two identifying sets differ exactly when some codeword
lies in one ball and not the other, which is how the question states it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **IDENTIFYING CODE is NP-complete.** Source: Charon, Hudry and Lobstein (2003),
Theorem 2.1. -/
public theorem_wanted identifyingCode_npComplete :
    identifyingCodeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L identifyingCodeDec

end MetaMathlibExt.Complexity.NPComplete.IdentifyingCode
