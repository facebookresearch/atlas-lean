/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SNAKE CUBE is NP-complete

Source:
Z. Abel, E. D. Demaine, M. L. Demaine, S. Eisenstat, J. Lynch and T. B. Schardl,
"Finding a Hamiltonian path in a cube with specified turns is hard", Journal of
Information Processing 21(3) (2013), 368-377, doi:10.2197/ipsjjip.21.368.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SnakeCubeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SnakeCube

/-!
# SNAKE CUBE is NP-complete

Abel, Demaine, Demaine, Eisenstat, Lynch and Schardl (2013), Section 2: "An (abstract) puzzle
of cubes is a sequence of Ss and Ts, representing straight cells and turn cells, respectively.
A configuration of a length-n abstract puzzle is a sequence of distinct cells `c₁, …, cₙ` and
faces `f₀, …, fₙ`, such that
* for each `1 ≤ i ≤ n`, `fᵢ₋₁` and `fᵢ` are distinct faces of cell `cᵢ`, and
* if the `i`th symbol in the puzzle is an S then `fᵢ₋₁` and `fᵢ` are opposite faces on cell
  `cᵢ`; if this symbol is a T, faces `fᵢ₋₁` and `fᵢ` are adjacent."
Cells are the unit cubes of the integer lattice, and co-located faces of adjacent cells are
identified. Section 1.1: the puzzle is a sequence of `N³` symbols, and the question is "whether
such a puzzle has a folded state in the shape of an `N × N × N` cube".

INSTANCE: a positive integer `N` (the cube's side length) and a sequence of `N³` symbols, each S
or T.
QUESTION: is there a configuration whose cells are exactly the cells of the `N × N × N` cube?

Representation. Symbols are `Bool`, `false` for S and `true` for T. A cell of the cube is its
coordinate vector `Fin 3 → Fin N`. A face of a cell is named by its outward normal
`(a, s) : Fin 3 × Bool`, the axis `a` and the sign `s` (`true` = positive). Two faces of one cell
are opposite when they have the same axis and different signs, and adjacent (share an edge) when
their axes differ. The configuration is listed from index `0` (the paper's `c₁`):
`e k` is the normal of face `f_k` on cell `c k` (the face the chain enters by) and `o k` the
normal of face `f_{k+1}` on cell `c k` (the face it leaves by). Face `f_{k+1}` is shared by
cells `c k` and `c (k+1)`, so `c (k+1)` is the neighbor of `c k` across normal `o k`, and on
`c (k+1)` the same face has the opposite normal: `e (k+1) = opp (o k)`. The S/T clause then
reads `e k = opp (o k)` for S and `(e k).1 ≠ (o k).1` for T; either way the two faces are
distinct. The first face `f₀` (`e 0`) and the last face `fₙ` (`o (n-1)`) are free, as in the
source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SNAKE CUBE is NP-complete.** Source: Abel, Demaine, Demaine, Eisenstat, Lynch and
Schardl (2013). -/
public theorem_wanted snakeCube_npComplete :
    snakeCubeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L snakeCubeDec

end MetaMathlibExt.Complexity.NPComplete.SnakeCube
