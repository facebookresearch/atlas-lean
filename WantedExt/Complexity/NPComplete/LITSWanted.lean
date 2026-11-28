/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LITS is NP-complete

Source:
M. Biro and C. Schmidt, "Computational complexity and bounds for Norinori and LITS", Proc. 33rd
European Workshop on Computational Geometry (EuroCG 2017), Malmö (2017), Theorem 2,
https://itn-web.it.liu.se/~chrsc91/papers/norinori-lits.pdf;
puzzle rules: Nikoli Co., Ltd., "LITS", https://www.nikoli.co.jp/en/puzzles/lits/.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LITSDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LITS

open MetaMathlibExt.Complexity.NPComplete.ChainedBlock (SameShape coords)

/-!
# LITS is NP-complete

Biro and Schmidt (2017): LITS is "played on an `m × n` square grid that has been partitioned
into connected polyomino regions"; "the solver places black squares in the regions such that
the final board satisfies the following properties:
1. The black squares form a connected polyomino.
2. Each polyomino region contains a connected black tetromino.
3. No two congruent tetrominos are adjacent.
4. Black squares may not build `2 × 2` squares."
They prove that "the problem of solving Norinori and LITS boards is NP-complete". Nikoli's rules
fix the details: "Color four consecutive squares (tetrominoes) in each of the areas surrounded
by bold lines. Similarly shaped rotated or reversed tetrominoes cannot touch, except at corners.
The colored squares must form a connected network. Colored squares cannot form `2 × 2` or larger
squares."

INSTANCE: an `m × n` grid partitioned into connected regions.
QUESTION: can squares be made black so that the black squares are connected, each region holds
exactly four black squares forming a connected tetromino, no two tetrominoes of different
regions that are congruent (by a rotation or a reflection) share an edge, and no `2 × 2` square
is all black?

Representation. The grid is given row by row, each square carrying the label of its region; a
region is the set of squares with one label (`WellFormed` requires it to be connected), so the
instance size is proportional to the area plus the binary length of the labels. Squares are
`Fin m × Fin n`, adjacent when they share an edge in Mathlib's grid graph
`pathGraph m □ pathGraph n`; connectedness of a set of squares is `SimpleGraph.Connected` of
the subgraph the grid graph induces on it. A choice of black squares is a function
`ℕ → ℕ → Bool` read on the grid. For property 3, the tetromino of a region is the set of
integer coordinates of its black squares (`ChainedBlock.coords`), and two tetrominoes are
congruent when they have the same shape in the sense of `ChainedBlock.SameShape`: one is the
image of the other under a rotation or reflection of the square lattice followed by a
translation.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LITS is NP-complete.** Source: Biro and Schmidt (2017), Theorem 2. -/
public theorem_wanted lits_npComplete :
    litsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L litsDec

end MetaMathlibExt.Complexity.NPComplete.LITS
