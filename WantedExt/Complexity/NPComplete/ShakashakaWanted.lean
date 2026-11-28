/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHAKASHAKA is NP-complete

Source:
E. D. Demaine, Y. Okamoto, R. Uehara and Y. Uno, "Computational complexity and an integer
programming model of Shakashaka", IEICE Transactions on Fundamentals of Electronics,
Communications and Computer Sciences E97-A(6) (2014), 1213-1219,
doi:10.1587/transfun.E97.A.1213 (conference version: 25th Canadian Conference on
Computational Geometry, CCCG 2013), Section 2 (definition) and Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShakashakaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Shakashaka

/-!
# SHAKASHAKA is NP-complete

An instance of Shakashaka is an `m × n` rectangular board of unit squares. Each unit square is
colored either white or black, and a black square may contain a number `i ∈ {0, …, 4}`. A
solution maps each white square to one of five options: left uncolored (white), or colored black
and white by a black half-square (an isosceles right triangle filling half the square) in one of
the four ways (a b/w square). It must satisfy: each black square that contains the number `i` has
exactly `i` b/w squares among its four (vertically or horizontally adjacent) neighbors, and each
connected white area forms a white rectangle (or square) (Demaine, Okamoto, Uehara and Uno,
Section 2). The question is whether the instance has a solution. The white rectangles may be
axis-parallel or tilted by `45°`, the only directions the boundaries of white areas can take.

Geometry: cell `(r, c)` (row `r`, column `c`) is the closed unit square
`[r, r + 1] × [c, c + 1]` of `ℝ × ℝ` (first coordinate: rows). The white area is the interior of
the union of the closed white parts of the white squares, so two white parts that meet only in a
point lie in different connected white areas, and white parts sharing a side merge. Its
connected components (`connectedComponentIn`) must each be an open axis-parallel rectangle
`{a₁ < x < a₂, b₁ < y < b₂}` or an open `45°` rectangle `{a₁ < x + y < a₂, b₁ < x - y < b₂}`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHAKASHAKA is NP-complete.** Source: Demaine, Okamoto, Uehara and Uno (2014),
Theorem 1. -/
public theorem_wanted shakashaka_npComplete :
    shakashakaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shakashakaDec

end MetaMathlibExt.Complexity.NPComplete.Shakashaka
