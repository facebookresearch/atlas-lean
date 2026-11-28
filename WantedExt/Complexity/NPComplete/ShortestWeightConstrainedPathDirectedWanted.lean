/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND30] SHORTEST
WEIGHT-CONSTRAINED PATH (p. 214; attributed there to N. Megiddo, 1977, private communication;
transformation from PARTITION), comment "Also NP-complete for directed graphs".
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDirected

open MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPath
  (ShortestWeightConstrainedPathInstance)

/-!
# SHORTEST WEIGHT-CONSTRAINED PATH for directed graphs is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a length `l(a) ∈ ℤ⁺` and a weight `w(a) ∈ ℤ⁺` for each
`a ∈ A`, specified vertices `s, t ∈ V`, and positive integers `K, W`.
QUESTION: is there a simple directed path in `G` from `s` to `t` with total weight `W` or less
and total length `K` or less?

This is SHORTEST WEIGHT-CONSTRAINED PATH ([ND30], `ShortestWeightConstrainedPathWanted`) for
directed graphs. The instance type is the parent's, read as arcs: `(u, v, l, w)` is the arc from
`u` to `v`. Since `(u, v)` and `(v, u)` are different arcs, the parent's `WellFormed` (which
forbids a reversed pair) and its orientation-free edge lookup do not apply; `WellFormed` and
`arcData` below are their directed counterparts. A simple directed path is
`DirectedTwoDisjointConnectingPaths.IsDirectedPath` (distinct vertices, first `s`, last `t`, an
arc from each vertex to the next); its total length (weight) is the sum of `l` (`w`) over its
consecutive vertex pairs. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete for directed graphs.** Source: Garey and
Johnson (1979), [ND30], comment (Megiddo, 1977, private communication). -/
public theorem_wanted shortestWeightConstrainedPathDirected_npComplete :
    shortestWeightConstrainedPathDirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestWeightConstrainedPathDirectedDec

end MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPathDirected
