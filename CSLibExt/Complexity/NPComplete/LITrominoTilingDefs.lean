/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TILING A POLYGON WITH L- AND I-TROMINOES: definitions

Source:
T. Horiyama, T. Ito, K. Nakatsuka, A. Suzuki and R. Uehara, "Complexity of tiling a polygon
with trominoes or bars", Discrete and Computational Geometry 58(3) (2017), 686-704,
doi:10.1007/s00454-017-9884-9, Theorem 3 (LI-tiling).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.List.Perm.Basic
public import CSLibExt.Complexity.NPComplete.RightTrominoTilingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LITrominoTiling

/-- An instance: the unit cells `(x, y)` of the polygon. -/
abbrev LITrominoTilingInstance := List (ℕ × ℕ)

/-- The grid graph on the unit cells of the quadrant: cells sharing an edge are adjacent. -/
abbrev CellGraph : SimpleGraph (ℕ × ℕ) := SimpleGraph.hasse ℕ □ SimpleGraph.hasse ℕ

/-- Well-formedness: the polygon has at least one cell, no cell is listed twice, and its cells
are connected along their edges. -/
def WellFormed (i : LITrominoTilingInstance) : Prop :=
  i ≠ [] ∧ i.Nodup ∧ (CellGraph.induce {x | x ∈ i}).Connected

/-- The three cells of the I-tromino at `p`: horizontal (`(x, y)`, `(x + 1, y)`, `(x + 2, y)`)
if `v = false`, vertical (`(x, y)`, `(x, y + 1)`, `(x, y + 2)`) if `v = true`. -/
def barCells (v : Bool) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if v then [(p.1, p.2), (p.1, p.2 + 1), (p.1, p.2 + 2)]
  else [(p.1, p.2), (p.1 + 1, p.2), (p.1 + 2, p.2)]

/-- The polygon is tiled by L- and I-trominoes: some placed L-trominoes (a rotation and a
`2 × 2` block position each) and placed I-trominoes (an orientation and a position each) cover
every cell of the polygon exactly once and nothing else. -/
def LITrominoTilingFeasible (i : LITrominoTilingInstance) : Prop :=
  ∃ ls : List (Fin 4 × (ℕ × ℕ)), ∃ bs : List (Bool × (ℕ × ℕ)),
    ((ls.flatMap fun t => RightTrominoTiling.trominoCells t.1 t.2) ++
      bs.flatMap fun t => barCells t.1 t.2).Perm i

open Classical in
/-- TILING A POLYGON WITH L- AND I-TROMINOES as a decision problem over bitstrings. -/
noncomputable def liTrominoTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LITrominoTilingInstance) x with
  | some i => decide (WellFormed i ∧ LITrominoTilingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LITrominoTiling
