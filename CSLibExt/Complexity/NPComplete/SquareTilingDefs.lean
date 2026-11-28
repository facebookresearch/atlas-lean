/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SQUARE-TILING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP13] SQUARE-TILING
(credited there to unpublished 1977 work of Garey, Johnson, and Papadimitriou);
E. D. Demaine and M. L. Demaine, "Jigsaw puzzles, edge matching, and polyomino
packing: connections and complexity", Graphs and Combinatorics 23 (2007),
suppl. 1, 195-208, doi:10.1007/s00373-007-0713-4 (records the attribution).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SquareTiling

/-- An instance: the color list `C`, the tile list `T` (a tile `(a, b, c, d)` is top, right,
bottom, left), and the side length `N`. -/
abbrev SquareTilingInstance := List ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `C` lists distinct colors, `T` lists distinct tiles, every
tile color is in `C`, and `0 < N ≤ |C|`. -/
def WellFormed (i : SquareTilingInstance) : Prop :=
  i.1.Nodup ∧ i.2.1.Nodup ∧
    (∀ t ∈ i.2.1, t.1 ∈ i.1 ∧ t.2.1 ∈ i.1 ∧ t.2.2.1 ∈ i.1 ∧ t.2.2.2 ∈ i.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1.length

/-- An `N × N` tiling: every position `(x, y)` with `x, y < N` gets a tile of `T`; the right
color of `f x y` equals the left color of `f (x + 1) y`, and the bottom color of `f x y`
equals the top color of `f x (y + 1)`, whenever both positions are in the square. -/
def SquareTilingFeasible (i : SquareTilingInstance) : Prop :=
  ∃ f : ℕ → ℕ → ℕ × ℕ × ℕ × ℕ,
    (∀ x < i.2.2, ∀ y < i.2.2, f x y ∈ i.2.1) ∧
    (∀ x y, x + 1 < i.2.2 → y < i.2.2 → (f x y).2.1 = (f (x + 1) y).2.2.2) ∧
    (∀ x y, x < i.2.2 → y + 1 < i.2.2 → (f x y).2.2.1 = (f x (y + 1)).1)

open Classical in
/-- SQUARE-TILING as a decision problem over bitstrings. -/
noncomputable def squareTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SquareTilingInstance) x with
  | some i => decide (WellFormed i ∧ SquareTilingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SquareTiling
