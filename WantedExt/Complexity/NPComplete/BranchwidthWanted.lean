/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BRANCHWIDTH is NP-complete

Source:
P. D. Seymour and R. Thomas, "Call routing and the ratcatcher", Combinatorica 14 (1994),
217-241, doi:10.1007/BF01215352 (branchwidth "is NP-hard for general graphs"; definitions in
Section 1, (1.1)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BranchwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Branchwidth

/-!
# BRANCHWIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer `K`. QUESTION: is the branchwidth of `G` at most
`K`?

Following Seymour and Thomas: a branch decomposition of `G` is a tree `T` in which every vertex
has valency `1` or `3`, with a bijection `τ` from `E` onto the set of leaves of `T`. Removing
an edge `xy` of `T` splits `T` into two components; the edges of `G` whose leaves lie in the
component of `x` form a set `A`, and `∂(A)` is the set of vertices of `G` incident with an edge
in `A` and with an edge in `E - A`. The width of the decomposition is the maximum of `|∂(A)|`
over the edges of `T`, and the branchwidth of `G` is the minimum width of a branch
decomposition, "or zero, if `|E(G)| ≤ 1`" (then `G` has no branch decomposition). So the
branchwidth is at most `K` exactly when `|E| ≤ 1` or some branch decomposition has every
`|∂(A)| ≤ K`.

The tree is a Mathlib `SimpleGraph` on `Fin m` (`SimpleGraph.IsTree`, valencies
`SimpleGraph.degree`); the component of `x` after removing `xy` is the set of vertices
reachable from `x` in `T.deleteEdges {s(x, y)}`. The edges of `G` are the entries of the edge
list, indexed by `Fin es.length`; under `WellFormed` there are no duplicate edges in either
orientation, so the entries are exactly `E`. `K` ranges over `ℕ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BRANCHWIDTH is NP-complete.** Source: Seymour and Thomas (1994). -/
public theorem_wanted branchwidth_npComplete :
    branchwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L branchwidthDec

end MetaMathlibExt.Complexity.NPComplete.Branchwidth
