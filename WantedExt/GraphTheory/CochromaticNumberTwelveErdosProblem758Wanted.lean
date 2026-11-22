/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The maximum cochromatic number of graphs on twelve vertices (Erdős Problem 758)

Erdős Problem 758 (Erdős and Gimbel): the cochromatic number of `G`, denoted by `ζ(G)`, is the
minimum number of colours needed to colour the vertices of `G` such that each colour class induces
either a complete graph or empty graph. Let `z(n)` be the maximum value of `ζ(G)` over all graphs
`G` with `n` vertices. Determine `z(n)` for small values of `z(n)`. In particular is it true that
`z(12) = 4`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.CochromaticNumberTwelveErdosProblem758Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #758, https://www.erdosproblems.com/758 (status
SOLVED). UnsolvedMath record UM-30007017 (`EP-758`), dataset ulamai/UnsolvedMath v1.8.0.

`ζ(G)` is MathlibExt's `SimpleGraph.cochromaticNumber` (colourings by `Fin k` in which every colour
class induces `⊥` or `⊤`, i.e. `SimpleGraph.Cocolorable`), finite for graphs on `Fin n` and taken
with `toNat`; `z(n)` is the `sSup` over the graphs on `Fin n` (a finite set of values). Only the "in
particular" question is formalized; the table of small values on the problem page (`n ≤ 19`) is not
stated.
-/

/-- `z(n)`: the maximum of the cochromatic number `ζ(G)` (MathlibExt's
`SimpleGraph.cochromaticNumber`, finite for a graph on `Fin n`) over all graphs `G` on `n`
vertices. -/
noncomputable def maxCochromaticNumber (n : ℕ) : ℕ :=
  sSup {z | ∃ G : SimpleGraph (Fin n), G.cochromaticNumber.toNat = z}

/-- Erdős Problem 758 (Erdős and Gimbel), "in particular": `z(12) = 4`. -/
def maxCochromaticNumberTwelve : Prop :=
  maxCochromaticNumber 12 = 4

/--
Resolved true: Erdős and Gimbel knew `4 ≤ z(12) ≤ 5`, and `z(12) = 4` reduces to graphs on `12`
vertices with `G` and its complement `K₄`-free; Mehta found computationally that the only such graph
(up to complement) with chromatic number `≥ 5` has cochromatic number `4`, so `z(12) = 4`;
erdosproblems.com/758 lists the problem as solved. Source: T. F. Bloom, Erdős Problems, Problem
#758, https://www.erdosproblems.com/758 (status SOLVED); resolution: erdosproblems.com/758
(computation by B. Mehta), erdosproblems.com/758: Bhavik Mehta found computationally that there is
exactly one graph (up to complement) on 12 vertices with G and its complement K₄-free and chromatic
number ≥ 5; it has cochromatic number 4, 'and hence this proves that indeed z(12) = 4' (Erdős and
Gimbel knew 4 ≤ z(12) ≤ 5), https://www.erdosproblems.com/758.
-/
public theorem_wanted maxCochromaticNumberTwelve_holds : maxCochromaticNumberTwelve

end MathlibExt.GraphTheory.CochromaticNumberTwelveErdosProblem758Wanted
