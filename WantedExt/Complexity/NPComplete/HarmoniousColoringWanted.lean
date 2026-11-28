/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HARMONIOUS COLORING is NP-complete

Source:
J. E. Hopcroft and M. S. Krishnamoorthy, "On the harmonious coloring of graphs", SIAM Journal
on Algebraic and Discrete Methods 4 (1983), 306-311, doi:10.1137/0604032.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HarmoniousColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring

/-!
# HARMONIOUS COLORING is NP-complete

A *harmonious coloring* of a graph is a proper vertex coloring in which every pair of colors
appears on at most one edge (Hopcroft and Krishnamoorthy 1983). INSTANCE: a graph `G = (V, E)`
and a positive integer `K`. QUESTION: does `G` have a harmonious coloring with at most `K`
colors?

A coloring with at most `K` colors is a Mathlib `SimpleGraph.Coloring` with colors `Fin K`
(proper by definition; not every color need be used). "Every pair of colors appears on at most
one edge" says: two edges `uv` and `xy` whose unordered color pairs `{c u, c v}` and
`{c x, c y}` coincide are the same edge, with unordered pairs as `Sym2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HARMONIOUS COLORING is NP-complete.** Source: Hopcroft and Krishnamoorthy (1983). -/
public theorem_wanted harmoniousColoring_npComplete :
    harmoniousColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L harmoniousColoringDec

end MetaMathlibExt.Complexity.NPComplete.HarmoniousColoring
