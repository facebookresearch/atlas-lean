/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLYOMINO PACKING: definitions

Source:
E. D. Demaine and M. L. Demaine, "Jigsaw puzzles, edge matching, and polyomino packing:
connections and complexity", Graphs and Combinatorics 23 (Suppl. 1) (2007), 195-208,
doi:10.1007/s00373-007-0713-4.
-/
module

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Combinatorics.Enumerative.LunnonDimensionDecomposition
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolyominoPacking

/-- An instance: the box width `a`, the box height `b`, and the pieces, each as the list of its
cells `(x, y)`. -/
abbrev PolyominoPackingInstance := ℕ × ℕ × List (List (ℕ × ℕ))

/-- A cell `(x, y)` as a lattice cell of `ℤ²`. -/
def toLattice (c : ℕ × ℕ) : latticeCell 2 := ![(c.1 : ℤ), (c.2 : ℤ)]

local instance : DecidableEq (latticeCell 2) := inferInstanceAs (DecidableEq (Fin 2 → ℤ))

/-- The cells of a piece as a finite set of lattice cells. -/
def pieceCells (p : List (ℕ × ℕ)) : Finset (latticeCell 2) := (p.map toLattice).toFinset

/-- Rotation of `ℤ²` by a right angle: `(x, y) ↦ (-y, x)`. -/
def rot (x : latticeCell 2) : latticeCell 2 := ![-x 1, x 0]

/-- The placement of a cell under `k` quarter turns followed by the translation by `t`. -/
def place (k : ℕ) (t x : latticeCell 2) : latticeCell 2 := fun j => rot^[k] x j + t j

/-- The cells of the `a × b` box. -/
def InBox (a b : ℕ) (x : latticeCell 2) : Prop :=
  0 ≤ x 0 ∧ x 0 < a ∧ 0 ≤ x 1 ∧ x 1 < b

/-- Well-formedness of an instance: the box has positive width and height, there is at least one
piece, and every piece lists distinct cells forming a polyomino. -/
def WellFormed (i : PolyominoPackingInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ i.2.2 ≠ [] ∧ ∀ p ∈ i.2.2, p.Nodup ∧ isPolycubeCells 2 (pieceCells p)

/-- The pieces pack the box exactly: each piece `j` is rotated by `k j` quarter turns and
translated by `t j` so that the placed cells lie in the box, no two placed cells coincide, and
every cell of the box is covered. -/
def PolyominoPackingFeasible (i : PolyominoPackingInstance) : Prop :=
  ∃ (k : Fin i.2.2.length → ℕ) (t : Fin i.2.2.length → latticeCell 2),
    (∀ j, ∀ x ∈ pieceCells i.2.2[j], InBox i.1 i.2.1 (place (k j) (t j) x)) ∧
    (∀ j j', ∀ x ∈ pieceCells i.2.2[j], ∀ x' ∈ pieceCells i.2.2[j'],
      place (k j) (t j) x = place (k j') (t j') x' → j = j' ∧ x = x') ∧
    ∀ y, InBox i.1 i.2.1 y → ∃ j, ∃ x ∈ pieceCells i.2.2[j], place (k j) (t j) x = y

open Classical in
/-- POLYOMINO PACKING as a decision problem over bitstrings. -/
noncomputable def polyominoPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolyominoPackingInstance) x with
  | some i => decide (WellFormed i ∧ PolyominoPackingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolyominoPacking
