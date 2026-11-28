/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED INSTANT INSANITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP15] GENERALIZED
INSTANT INSANITY;
E. Robertson and I. Munro, "NP-completeness, puzzles and games", Utilitas
Mathematica 13 (1978), 99-116.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedInstantInsanityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity

/-!
# GENERALIZED INSTANT INSANITY is NP-complete

INSTANCE: a set `Q` of cubes and a set `C` of colors with `|Q| = |C|`, and for each cube
`q ∈ Q` an assignment of a color in `C` to each of the six faces of `q`. QUESTION: can the
cubes in `Q` be stacked in a vertical column such that each of the colors in `C` appears
exactly once on each of the four sides of the column?

A cube is given by its three pairs of opposite faces. Placing a cube in the column chooses a
front-back axis and a different right-left axis (the remaining axis is vertical and hidden),
and which face of each chosen pair faces front and right. These choices give exactly the side
colors of the 24 rotations of a cube: for each of the 3 vertical axes, the rotations about it
together with the half-turn that flips the cube over realize all 8 ways to put one remaining
pair front-back and the other right-left, in either order. The order of the cubes in the
column does not affect the side colors. Colors are `0, ..., |C| - 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED INSTANT INSANITY is NP-complete.** Source: Garey and Johnson (1979), [GP15];
Robertson and Munro (1978). -/
public theorem_wanted generalizedInstantInsanity_npComplete :
    generalizedInstantInsanityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedInstantInsanityDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedInstantInsanity
