/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TANTRIX ROTATION PUZZLE: definitions

Source:
M. Holzer and W. Holzer, "Tantrix rotation puzzles are intractable", Discrete Applied
Mathematics 144 (2004), 345-358, doi:10.1016/j.dam.2003.11.011;
D. Baumeister and J. Rothe, "The three-color and two-color Tantrix rotation puzzle problems
are NP-complete via parsimonious reductions", Information and Computation 207 (2009),
1119-1139, doi:10.1016/j.ic.2009.03.001 (arXiv:0711.1827), Section 2.2 (the formal definition
of the problem, following Holzer and Holzer).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzle

/-- An instance: the placed tiles, each a position `(a, b)` and a color sequence (six colors,
read clockwise). -/
abbrev TantrixRotationPuzzleInstance := List ((ℕ × ℕ) × List ℕ)

/-- The color sequence of one of the 56 Tantrix tiles: six colors among `0, 1, 2, 3`, each
color that occurs occurs on exactly two edges (so there are three lines of distinct colors),
and the three lines are not all straight. -/
def IsTantrixTile (s : List ℕ) : Prop :=
  s.length = 6 ∧ (∀ c ∈ s, c < 4 ∧ s.count c = 2) ∧
    ¬ (s.getD 0 0 = s.getD 3 0 ∧ s.getD 1 0 = s.getD 4 0 ∧ s.getD 2 0 = s.getD 5 0)

/-- The neighbor faced by edge `e` (`0` is the top edge, then clockwise) is at this offset. -/
def edgeDir : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | 1 => (1, 0)
  | 2 => (0, -1)
  | 3 => (-1, -1)
  | 4 => (-1, 0)
  | _ => (0, 1)

/-- The color at edge `e` of a tile with color sequence `s` after rotating it by `r` steps. -/
def colorAt (s : List ℕ) (r e : ℕ) : ℕ :=
  s.getD ((e + r) % 6) 0

/-- Well-formedness of an instance: no two tiles share a position, and every tile is a Tantrix
tile. -/
def WellFormed (i : TantrixRotationPuzzleInstance) : Prop :=
  (i.map Prod.fst).Nodup ∧ ∀ t ∈ i, IsTantrixTile t.2

/-- A solution: a rotation `rot j` of every tile `j` such that whenever tile `k` is the
neighbor of tile `j` across edge `e` of tile `j`, the colors at that edge of `j` and at the
opposite edge `e + 3` of `k` agree. -/
def TantrixRotationPuzzleFeasible (i : TantrixRotationPuzzleInstance) : Prop :=
  ∃ rot : ℕ → ℕ, ∀ j < i.length, ∀ k < i.length, ∀ e < 6,
    ((i.getD k ((0, 0), [])).1.1 : ℤ) = (i.getD j ((0, 0), [])).1.1 + (edgeDir e).1 →
    ((i.getD k ((0, 0), [])).1.2 : ℤ) = (i.getD j ((0, 0), [])).1.2 + (edgeDir e).2 →
    colorAt (i.getD j ((0, 0), [])).2 (rot j) e =
      colorAt (i.getD k ((0, 0), [])).2 (rot k) ((e + 3) % 6)

open Classical in
/-- TANTRIX ROTATION PUZZLE as a decision problem over bitstrings. -/
noncomputable def tantrixRotationPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TantrixRotationPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ TantrixRotationPuzzleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzle
