/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TANTRIX ROTATION PUZZLE with three or two colors: definitions

Source:
D. Baumeister and J. Rothe, "The three-color and two-color Tantrix rotation puzzle problems
are NP-complete via parsimonious reductions", Information and Computation 207 (2009),
1119-1139, doi:10.1016/j.ic.2009.03.001 (arXiv:0711.1827).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TantrixRotationPuzzleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzleThreeTwoColors

open MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzle

/-- Well-formedness of a 3-TRP instance: a Tantrix rotation puzzle instance whose tiles use only
red, yellow and blue, i.e. tiles of `T₃`. -/
def WellFormedThree (i : TantrixRotationPuzzleInstance) : Prop :=
  WellFormed i ∧ ∀ t ∈ i, ∀ c ∈ t.2, c < 3

/-- The color sequences of the tile set `T₂` (Baumeister and Rothe, Table 2), with red `0` and
blue `2`. -/
def tileSetTwo : List (List ℕ) :=
  [[2, 2, 0, 0, 0, 0], [0, 0, 2, 2, 2, 2], [2, 0, 0, 2, 0, 0], [0, 2, 2, 0, 2, 2],
    [0, 2, 0, 0, 0, 2], [2, 0, 2, 2, 2, 0], [2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 0, 0]]

/-- Well-formedness of a 2-TRP instance: no two tiles share a position, and every tile is a tile
of `T₂`, given by one of its color sequences (a cyclic shift of a sequence of `tileSetTwo`). -/
def WellFormedTwo (i : TantrixRotationPuzzleInstance) : Prop :=
  (i.map Prod.fst).Nodup ∧ ∀ t ∈ i, ∃ s ∈ tileSetTwo, ∃ r < 6, t.2 = s.rotate r

open Classical in
/-- 3-TRP as a decision problem over bitstrings. -/
noncomputable def threeColorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TantrixRotationPuzzleInstance) x with
  | some i => decide (WellFormedThree i ∧ TantrixRotationPuzzleFeasible i)
  | none => false

open Classical in
/-- 2-TRP as a decision problem over bitstrings. -/
noncomputable def twoColorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TantrixRotationPuzzleInstance) x with
  | some i => decide (WellFormedTwo i ∧ TantrixRotationPuzzleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzleThreeTwoColors
