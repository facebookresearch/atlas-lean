/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TANTRIX ROTATION PUZZLE with three or two colors is NP-complete

Source:
D. Baumeister and J. Rothe, "The three-color and two-color Tantrix rotation puzzle problems
are NP-complete via parsimonious reductions", Information and Computation 207 (2009),
1119-1139, doi:10.1016/j.ic.2009.03.001 (arXiv:0711.1827).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TantrixRotationPuzzleWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzleThreeTwoColors

open MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzle

/-!
# TANTRIX ROTATION PUZZLE with three or two colors is NP-complete

Baumeister and Rothe's `k`-TRP for `k = 3` and `k = 2`: the Tantrix rotation puzzle of
`TantrixRotationPuzzleWanted` (positions, adjacency, rotations and the matching condition are
the same) with the tiles restricted to a tile set `T₃` or `T₂`.

- `T₃`: the Tantrix tiles whose line colors lie in a fixed set `C₃` of three colors, here red,
  yellow and blue (`0`, `1`, `2`); these are the 14 tiles of the paper's Table 3.
- `T₂`: for a fixed set `C₂` of two colors, here red and blue (`0`, `2`), the paper fixes the
  eight tiles of its Table 2 (the same color may be used for several lines), with color
  sequences `bbrrrr`, `rrbbbb`, `brrbrr`, `rbbrbb`, `rbrrrb`, `brbbbr`, `bbbbbb`, `rrrrrr`.

`T₂` is not contained in `T₃`, so the paper proves each problem NP-complete separately
(Corollaries 3.3 and 3.6 of the arXiv version); both are stated here.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **The three-color Tantrix rotation puzzle (3-TRP) is NP-complete.** Source: Baumeister and
Rothe (2009). -/
public theorem_wanted threeColor_npComplete :
    threeColorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorDec

/-- **The two-color Tantrix rotation puzzle (2-TRP) is NP-complete.** Source: Baumeister and
Rothe (2009). -/
public theorem_wanted twoColor_npComplete :
    twoColorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoColorDec

end MetaMathlibExt.Complexity.NPComplete.TantrixRotationPuzzleThreeTwoColors
