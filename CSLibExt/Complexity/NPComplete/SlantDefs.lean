/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SLANT: definitions

Source:
J. Lynch and J. Spalding-Jamieson, "Slant/Gokigen Naname is NP-complete, and some variations are
in P", arXiv:2502.13536 (2025) (Section 1: the rules; Theorem 7).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Slant

/-- An instance: the vertices of the board row by row, each with `(numbered, number)`. -/
abbrev SlantInstance := List (List (Bool × ℕ))

/-- The number `H` of rows of squares. -/
def height (i : SlantInstance) : ℕ := i.length - 1

/-- The number `W` of columns of squares. -/
def width (i : SlantInstance) : ℕ := (i.headD []).length - 1

/-- The clue `(numbered, number)` of vertex `(r, c)`. -/
def clue (i : SlantInstance) (r c : ℕ) : Bool × ℕ := (i.getD r []).getD c (false, 0)

/-- Well-formedness: at least one square (two rows and two columns of vertices), rows of equal
length, numbers in `{0, …, 4}`, and the number `0` on every unnumbered vertex. -/
def WellFormed (i : SlantInstance) : Prop :=
  2 ≤ i.length ∧ 2 ≤ (i.headD []).length ∧ (∀ row ∈ i, row.length = (i.headD []).length) ∧
    ∀ row ∈ i, ∀ v ∈ row, v.2 ≤ 4 ∧ (v.1 = false → v.2 = 0)

/-- The graph of the diagonals of the filling `d` of the `H × W` squares, on the lattice points:
square `(r, c)` joins `(r, c)` and `(r + 1, c + 1)` if `d r c = true`, and `(r, c + 1)` and
`(r + 1, c)` otherwise. -/
def diagGraph (H W : ℕ) (d : ℕ → ℕ → Bool) : SimpleGraph (ℕ × ℕ) :=
  SimpleGraph.fromRel fun u v => ∃ r < H, ∃ c < W,
    (d r c = true ∧ u = (r, c) ∧ v = (r + 1, c + 1)) ∨
      (d r c = false ∧ u = (r, c + 1) ∧ v = (r + 1, c))

/-- The filling `d` solves the board: its diagonals form no cycle, and every numbered vertex is
adjacent to exactly that many diagonals. -/
def Solves (i : SlantInstance) (d : ℕ → ℕ → Bool) : Prop :=
  (diagGraph (height i) (width i) d).IsAcyclic ∧
    ∀ r ≤ height i, ∀ c ≤ width i, (clue i r c).1 = true →
      ((diagGraph (height i) (width i) d).neighborSet (r, c)).ncard = (clue i r c).2

/-- Some filling solves the board. -/
def SlantFeasible (i : SlantInstance) : Prop :=
  ∃ d : ℕ → ℕ → Bool, Solves i d

open Classical in
/-- SLANT as a decision problem over bitstrings. -/
noncomputable def slantDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SlantInstance) x with
  | some i => decide (WellFormed i ∧ SlantFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Slant
