/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED ELIMINATION ORDERING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT46] DIRECTED
ELIMINATION ORDERING;
D. J. Rose and R. E. Tarjan, "Algorithmic aspects of vertex elimination on
directed graphs", SIAM Journal on Applied Mathematics 34 (1978), 176-197,
doi:10.1137/0134014.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DirectedEliminationOrderingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedEliminationOrdering

/-!
# DIRECTED ELIMINATION ORDERING is NP-complete

INSTANCE: a directed graph `G = (V, A)` and a non-negative integer `K`.
QUESTION: is there an elimination ordering for `G` with fill-in `K` or less, i.e., a one-to-one
function `f : V → {1, 2, ..., |V|}` such that there are at most `K` pairs of vertices
`(u, v) ∈ (V × V) - A` with the property that `G` contains a directed path from `u` to `v` that
only passes through vertices `w` satisfying `f(w) < min {f(u), f(v)}`?

A directed path is a list of distinct vertices `u = x₀, x₁, ..., xₖ = v` with `(xⱼ, xⱼ₊₁) ∈ A`;
it "passes through" its interior vertices `x₁, ..., xₖ₋₁`. Since the vertices of a path are
distinct, the pairs counted have `u ≠ v`. Rose and Tarjan (1978, Lemma 1) show that these pairs
are exactly the arcs added by eliminating the vertices in the order `f`, where eliminating `w`
adds an arc `(x, y)` for every remaining `x ≠ y` with `(x, w)` and `(w, y)` present.

Directed graphs are given by arc lists without loops or repeated arcs (Rose and Tarjan:
`E ⊆ {(v, w) | v ≠ w}`), read as Mathlib `Digraph`s. Positions are 0-based:
`f : Fin |V| → Fin |V|`; only comparisons of positions matter.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DIRECTED ELIMINATION ORDERING is NP-complete.** Source: Garey and Johnson (1979),
[GT46]; Rose and Tarjan (1978). -/
public theorem_wanted directedEliminationOrdering_npComplete :
    directedEliminationOrderingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedEliminationOrderingDec

end MetaMathlibExt.Complexity.NPComplete.DirectedEliminationOrdering
