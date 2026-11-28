/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B-CHROMATIC NUMBER is NP-complete

Source:
R. W. Irving and D. F. Manlove, "The b-chromatic number of a graph", Discrete Applied
Mathematics 91 (1999), 127-141, doi:10.1016/S0166-218X(98)00146-2 (Theorem 3.3).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BChromaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BChromaticNumber

/-!
# B-CHROMATIC NUMBER is NP-complete

A b-colouring of a graph `G` with `k` colours is a proper colouring of `G` with colours
`1, …, k` in which every colour class contains a vertex adjacent to a vertex of every other
colour. The b-chromatic number `φ(G)` is the largest `k` for which `G` has a b-colouring with
`k` colours.

INSTANCE: a graph `G = (V, E)` and an integer `K`. QUESTION: is `φ(G) ≥ K`, i.e., does `G` have
a b-colouring with `k` colours for some `k ≥ K`?

This is Irving and Manlove's decision problem ("determine whether `φ(G) ≥ K`, for a given
integer `K` and graph `G`"). Since b-colourings need not exist for every number of colours
between `χ(G)` and `φ(G)`, the question asks for some `k ≥ K`, not for exactly `K` colours. A
proper colouring with `k` colours is Mathlib's `SimpleGraph.Coloring` into `Fin k`; every
colour class is nonempty because it contains a vertex of the b-condition. `K` ranges over `ℕ`
(a negative `K` is a trivial yes-instance, as is `K = 0`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **B-CHROMATIC NUMBER is NP-complete.** Source: Irving and Manlove (1999), Theorem 3.3. -/
public theorem_wanted bChromaticNumber_npComplete :
    bChromaticNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bChromaticNumberDec

end MetaMathlibExt.Complexity.NPComplete.BChromaticNumber
