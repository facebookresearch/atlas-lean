/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILING A REGION WITH RIGHT TROMINOES is NP-complete

Source:
C. Moore and J. M. Robson, "Hard tiling problems with simple tiles", Discrete and
Computational Geometry 26(4) (2001), 573-590, doi:10.1007/s00454-001-0047-6, Section 3
("the existence problem is NP-complete for the set of tiles consisting only of the right
tromino (with rotations allowed)"; arXiv:math/0003039).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RightTrominoTilingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RightTrominoTiling

/-!
# TILING A REGION WITH RIGHT TROMINOES is NP-complete

INSTANCE: a finite region of the square lattice, that is, a finite set of unit cells.
QUESTION: can the region be tiled by copies of the right tromino, rotations allowed, that is,
partitioned into sets of three cells each forming a right (L-shaped) tromino?

A cell is given by its lattice coordinates `(x, y)`. Coordinates are natural numbers; tiling
is invariant under translation, and every finite region translates into the quadrant
`x, y ≥ 0`. The right tromino is a `2 × 2` block of cells with one corner cell removed, and its
four rotations are the four choices of the removed corner (its reflections are rotations).
A tile whose cells lie in the quadrant has the lower left corner of its `2 × 2` block in the
quadrant too, so placing blocks at natural coordinates gives every copy.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TILING A REGION WITH RIGHT TROMINOES is NP-complete.** Source: Moore and Robson (2001),
Section 3. -/
public theorem_wanted rightTrominoTiling_npComplete :
    rightTrominoTilingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rightTrominoTilingDec

end MetaMathlibExt.Complexity.NPComplete.RightTrominoTiling
