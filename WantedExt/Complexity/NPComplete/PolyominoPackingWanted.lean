/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLYOMINO PACKING is NP-complete

Source:
E. D. Demaine and M. L. Demaine, "Jigsaw puzzles, edge matching, and polyomino packing:
connections and complexity", Graphs and Combinatorics 23 (Suppl. 1) (2007), 195-208,
doi:10.1007/s00373-007-0713-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Combinatorics.Enumerative.LunnonDimensionDecomposition
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolyominoPacking

/-!
# POLYOMINO PACKING is NP-complete

Given polyomino pieces and a rectangular box, can the pieces be exactly packed into the box, that
is, placed so that they use every piece "to fill exactly the target shape, with no overlap or
blank space" (Demaine and Demaine 2007, Section 1)? Theorem 1 of Demaine and Demaine: "It is
(strongly) NP-complete to decide whether `n` given rectangular pieces, sized `1 × x₁, ..., 1 × xₙ`
where the `xᵢ`'s are positive integers bounded above by a polynomial in `n`, can be exactly
packed into a specified rectangular box of area `x₁ + ... + xₙ`"; these rectangles are
polyominoes, so packing general polyominoes into a rectangle is NP-complete (membership: "it is
easy to verify the validity of a packing or tiling in polynomial time"). Corollary 3 gives the
same for pieces fitting in `Θ(log n) × Θ(log n)` rectangles and a square box.

A piece is given as the list of its unit cells (integer points, non-negative coordinates; the
problem is translation-invariant) and must be a polyomino, i.e. a 2-dimensional polycube in the
sense of the shared `isPolycubeCells` (a nonempty face-connected cell set). As in the proof of
Theorem 1 ("the pieces must be placed on the integer grid of the box, and in particular can be
rotated only by multiples of 90°"), a placement rotates a piece by a multiple of a right angle
and translates it by an integer vector; the box with width `a` and height `b` is the set of
cells `(x, y)` with `0 ≤ x < a` and `0 ≤ y < b`. Pieces are not reflected; for rectangular
pieces, which carry the hardness of Theorem 1, a reflection is a rotation.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **POLYOMINO PACKING is NP-complete.** Source: Demaine and Demaine (2007), Theorem 1 and
Corollary 3. -/
public theorem_wanted polyominoPacking_npComplete :
    polyominoPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L polyominoPackingDec

end MetaMathlibExt.Complexity.NPComplete.PolyominoPacking
