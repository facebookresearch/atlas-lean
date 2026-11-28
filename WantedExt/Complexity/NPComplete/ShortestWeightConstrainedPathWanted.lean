/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND30] SHORTEST
WEIGHT-CONSTRAINED PATH (attributed there to N. Megiddo, 1977, private
communication; transformation from PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPath

/-!
# SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ⁺` and a weight `w(e) ∈ ℤ⁺` for each
`e ∈ E`, specified vertices `s, t ∈ V`, and positive integers `K, W`.
QUESTION: is there a simple path in `G` from `s` to `t` with total weight `W` or less and total
length `K` or less?

A simple path is a Mathlib `SimpleGraph.Walk` that `IsPath`; its total length (weight) is the
sum of `l` (`w`) over the edges it traverses, read from the edge list. Numbers use the binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete.** Source: Garey and Johnson (1979),
[ND30] (Megiddo, 1977, private communication). -/
public theorem_wanted shortestWeightConstrainedPath_npComplete :
    shortestWeightConstrainedPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestWeightConstrainedPathDec

end MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPath
