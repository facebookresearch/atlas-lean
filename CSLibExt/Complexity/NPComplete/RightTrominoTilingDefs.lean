/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILING A REGION WITH RIGHT TROMINOES: definitions

Source:
C. Moore and J. M. Robson, "Hard tiling problems with simple tiles", Discrete and
Computational Geometry 26(4) (2001), 573-590, doi:10.1007/s00454-001-0047-6, Section 3
("the existence problem is NP-complete for the set of tiles consisting only of the right
tromino (with rotations allowed)"; arXiv:math/0003039).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RightTrominoTiling

/-- An instance: the cells `(x, y)` of the region. -/
abbrev RightTrominoTilingInstance := List (ℕ × ℕ)

/-- Well-formedness of an instance: the cells are distinct, so the list is a set of cells. -/
def WellFormed (i : RightTrominoTilingInstance) : Prop :=
  i.Nodup

/-- The four cells of the `2 × 2` block whose lower left cell is `p`. -/
def blockCells (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(p.1, p.2), (p.1 + 1, p.2), (p.1, p.2 + 1), (p.1 + 1, p.2 + 1)]

/-- The three cells of the right tromino in rotation `o`, in the `2 × 2` block at `p`: the
block without its cell number `o`. -/
def trominoCells (o : Fin 4) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  (blockCells p).eraseIdx o

/-- The region is tiled by right trominoes: some list of placed trominoes (a rotation and a
block position each) covers every cell of the region exactly once and nothing else, i.e. the
cells of the tiles, counted with multiplicity, are a permutation of the region's cells. -/
def RightTrominoTilingFeasible (i : RightTrominoTilingInstance) : Prop :=
  ∃ tiles : List (Fin 4 × (ℕ × ℕ)), (tiles.flatMap fun t => trominoCells t.1 t.2).Perm i

open Classical in
/-- TILING A REGION WITH RIGHT TROMINOES as a decision problem over bitstrings. -/
noncomputable def rightTrominoTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RightTrominoTilingInstance) x with
  | some i => decide (WellFormed i ∧ RightTrominoTilingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RightTrominoTiling
