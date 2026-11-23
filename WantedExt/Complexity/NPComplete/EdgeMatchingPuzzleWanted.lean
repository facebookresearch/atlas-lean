/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE-MATCHING PUZZLE is NP-complete

Source:
E. D. Demaine and M. L. Demaine, "Jigsaw puzzles, edge matching, and polyomino packing:
connections and complexity", Graphs and Combinatorics 23 (2007), suppl. 1, 195-208,
doi:10.1007/s00373-007-0713-4 (Theorem 3).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeMatchingPuzzle

/-!
# EDGE-MATCHING PUZZLE is NP-complete

INSTANCE: `n` unit square tiles with a color on each edge, and a target rectangle.
QUESTION: can the tiles, each used exactly once and possibly rotated, fill the rectangle so
that adjacent tiles have matching colors along their common edge?

A tile is `(t, r, b, l)`: its top, right, bottom and left colors. Rotating a tile a quarter turn
clockwise moves its top color to the right side (`rotate`); a placed tile is turned by `0` to `3`
quarter turns (tiles are not reflected). The rectangle has `h` rows and `w` columns; position
`(y, x)` is row `y` (top to bottom) and column `x` (left to right). A solution is a bijection from
positions to tiles plus a rotation per position, such that the right color of each placed tile
equals the left color of the tile to its right, and its bottom color equals the top color of the
tile below it. The outer boundary is unconstrained. A bijection exists only when `n = h w`.

Demaine and Demaine prove NP-completeness for a `√n × √n` square box (Theorem 3); square boxes
are rectangles, so the rectangle version is NP-hard too, and it is in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the tiles `(top, right, bottom, left)`, the number of rows `h`, and the number
of columns `w` of the rectangle. -/
abbrev EdgeMatchingPuzzleInstance := List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ

/-- A quarter turn clockwise: the new top, right, bottom and left colors are the old left, top,
right and bottom colors. -/
def rotate (t : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ := (t.2.2.2, t.1, t.2.1, t.2.2.1)

/-- The tile at position `(y, x)`: tile `place (y, x)`, turned `turns (y, x)` quarter turns. -/
def placed (i : EdgeMatchingPuzzleInstance) (place : Fin i.2.1 × Fin i.2.2 → Fin i.1.length)
    (turns : Fin i.2.1 × Fin i.2.2 → Fin 4) (p : Fin i.2.1 × Fin i.2.2) : ℕ × ℕ × ℕ × ℕ :=
  rotate^[turns p] (i.1.get (place p))

/-- Well-formedness of an instance: the rectangle has positive height and width. -/
def WellFormed (i : EdgeMatchingPuzzleInstance) : Prop :=
  0 < i.2.1 ∧ 0 < i.2.2

/-- The tiles fill the rectangle, each exactly once (`place` is a bijection), with rotations
`turns`, so that horizontally and vertically adjacent edges have matching colors. -/
def EdgeMatchingPuzzleFeasible (i : EdgeMatchingPuzzleInstance) : Prop :=
  ∃ place : Fin i.2.1 × Fin i.2.2 → Fin i.1.length, Function.Bijective place ∧
    ∃ turns : Fin i.2.1 × Fin i.2.2 → Fin 4,
      (∀ (y : Fin i.2.1) (x x' : Fin i.2.2), (x' : ℕ) = (x : ℕ) + 1 →
        (placed i place turns (y, x)).2.1 = (placed i place turns (y, x')).2.2.2) ∧
      (∀ (y y' : Fin i.2.1) (x : Fin i.2.2), (y' : ℕ) = (y : ℕ) + 1 →
        (placed i place turns (y, x)).2.2.1 = (placed i place turns (y', x)).1)

open Classical in
/-- EDGE-MATCHING PUZZLE as a decision problem over bitstrings. -/
noncomputable def edgeMatchingPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeMatchingPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ EdgeMatchingPuzzleFeasible i)
  | none => false

/-- **EDGE-MATCHING PUZZLE is NP-complete.** Source: Demaine and Demaine (2007), Theorem 3. -/
public theorem_wanted edgeMatchingPuzzle_npComplete :
    edgeMatchingPuzzleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeMatchingPuzzleDec

end MetaMathlibExt.Complexity.NPComplete.EdgeMatchingPuzzle
