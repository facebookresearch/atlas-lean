/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH WITH FORBIDDEN PAIRS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS;
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of
program test paths", IEEE Transactions on Software Engineering SE-2 (1976), 227-231,
doi:10.1109/TSE.1976.233819.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathWithForbiddenPairsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairs

/-!
# PATH WITH FORBIDDEN PAIRS is NP-complete

Given a directed graph `G = (V, A)`, specified vertices `s, t ∈ V`, and a collection
`C = {(a₁, b₁), ..., (aₙ, bₙ)}` of pairs of vertices from `V`, is there a directed path from
`s` to `t` in `G` that contains at most one vertex from each pair in `C`?

The vertices are `0, ..., m - 1`, the arcs and the pairs are lists of ordered pairs. A path
is a nonempty list of distinct vertices, starting at `s` and ending at `t`, in which
consecutive vertices are joined by an arc (`List.IsChain`); for `s = t` the one-vertex path
`[s]` counts. "At most one vertex from each pair" means that a path containing both `aⱼ` and
`bⱼ` has `aⱼ = bⱼ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATH WITH FORBIDDEN PAIRS is NP-complete.** Source: Garey and Johnson (1979), [GT54];
Gabow, Maheshwari and Osterweil (1976). -/
public theorem_wanted pathWithForbiddenPairs_npComplete :
    pathWithForbiddenPairsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathWithForbiddenPairsDec

end MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairs
