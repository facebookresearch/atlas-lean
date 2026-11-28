/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTANGULAR SPIRAL GALAXIES is NP-complete

Source:
E. D. Demaine, M. Löffler and C. Schmidt, "Rectangular Spiral Galaxies are still hard",
Computational Geometry 110 (2023), 101949, doi:10.1016/j.comgeo.2022.101949, Section 1
(Rectangular Galaxies) and Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RectangularSpiralGalaxiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectangularSpiralGalaxies

/-!
# RECTANGULAR SPIRAL GALAXIES is NP-complete

Rectangular Galaxies (Demaine, Löffler and Schmidt, Section 1) is Spiral Galaxies in which the
polyomino galaxies are required to be rectangles, an additional restriction beyond `180°`
rotational symmetry around the unique center contained in each rectangle. The question is
whether the puzzle has such a solution. Demaine, Löffler and Schmidt show it NP-complete even
for puzzles whose solutions use only `1 × 1`, `1 × 3` and `3 × 1` galaxies (Theorem 2).

The board, the centres (doubled coordinates) and the galaxy conditions are those of
`MetaMathlibExt.Complexity.NPComplete.SpiralGalaxies`; the extra condition is that every galaxy
is an axis-parallel rectangle of cells, rows `r₁ ≤ r < r₂` and columns `c₁ ≤ c < c₂`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECTANGULAR SPIRAL GALAXIES is NP-complete.** Source: Demaine, Löffler and Schmidt (2023),
Theorem 2. -/
public theorem_wanted rectangularSpiralGalaxies_npComplete :
    rectangularSpiralGalaxiesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectangularSpiralGalaxiesDec

end MetaMathlibExt.Complexity.NPComplete.RectangularSpiralGalaxies
