/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZEIGER is NP-complete

Source:
S. Ruangwises, "NP-completeness and physical zero-knowledge proofs for Zeiger", in WALCOM:
Algorithms and Computation, Lecture Notes in Computer Science (2025), 312-325,
doi:10.1007/978-981-96-2845-2_20 (arXiv:2409.14308).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ZeigerDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zeiger

/-!
# ZEIGER is NP-complete

INSTANCE: a rectangular grid, each cell having an arrow pointing in a horizontal or vertical
direction; some cells also contain a positive integer.
QUESTION: can a positive integer be filled into every unnumbered cell so that the integer in each
cell equals the number of different integers in all cells along the direction the arrow in that
cell points to?

The grid is given explicitly, row by row: each cell is `(d, a)` with arrow `d` (`0` up, `1`
right, `2` down, `3` left) and `a = 0` (no number) or the given positive integer `a`. The cells
along the arrow of cell `(r, c)` are the cells strictly beyond it in that direction, up to the
edge of the grid (`Ray`): for an up arrow the cells `(r', c)` with `r' < r`, and so on. A
solution is a positive integer `v x` in every cell, equal to the given integer where there is
one, such that `v x` is the number of distinct values of `v` on the ray of `x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ZEIGER is NP-complete.** Source: Ruangwises (2025). -/
public theorem_wanted zeiger_npComplete :
    zeigerDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zeigerDec

end MetaMathlibExt.Complexity.NPComplete.Zeiger
