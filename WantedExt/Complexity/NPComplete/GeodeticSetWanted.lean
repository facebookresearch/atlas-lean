/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEODETIC SET is NP-complete

Source:
M. Atici, "Computational complexity of geodetic set", International Journal of Computer
Mathematics 79(5) (2002), 587-591, doi:10.1080/00207160210954.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeodeticSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeodeticSet

/-!
# GEODETIC SET is NP-complete

INSTANCE: a connected graph `G = (V, E)` (finite, simple, undirected) and a positive integer
`K`.
QUESTION: is there a set `S ⊆ V` with `|S| ≤ K` such that every vertex lies on some shortest
path between two vertices of `S`?

A vertex `x` lies on a shortest `u`-`v` path when some walk from `u` to `v` of length
`G.dist u v` (Mathlib's distance; the graph is connected) passes through `x`; a shortest walk is
a path. The two vertices of `S` may coincide, so every vertex of `S` is covered by its own
trivial path.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GEODETIC SET is NP-complete.** Source: Atici (2002). -/
public theorem_wanted geodeticSet_npComplete :
    geodeticSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geodeticSetDec

end MetaMathlibExt.Complexity.NPComplete.GeodeticSet
