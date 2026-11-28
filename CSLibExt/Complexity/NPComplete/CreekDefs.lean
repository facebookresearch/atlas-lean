/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Finset.Card

/-!
# CREEK: definitions

Uejima and Oe (Section 1) define the Creek Decision Problem (the 4-Creek Decision Problem):
INSTANCE: a square grid `B` of size `m × n`, with circled integers in `{0, 1, 2, 3, 4}` placed
at some lattice points on `B`.
QUESTION: can some squares of `B` be colored blue while satisfying (1) the number inside each
circle dictates how many of the squares touched by the circle are colored blue, and (2) all
uncolored squares form a single contiguous region connected by edges?
They prove it NP-complete (Theorem 1).

The board is given explicitly, as its `(m + 1) × (n + 1)` lattice points row by row: entry `b`
of row `a` is `0` when no circle sits at the lattice point `(a, b)`, and `d + 1` when a circle
with the number `d` sits there; so the input size grows with the area of the board, as for the
board in the source. The squares are `Fin m × Fin n`, adjacent when they share an edge in
Mathlib's grid graph `pathGraph m □ pathGraph n`. The lattice point `(a, b)` is a corner of
(touches) the squares `(r, c)` with `r ∈ {a - 1, a}` and `c ∈ {b - 1, b}` that lie on the grid.
Rule (2) says that the uncolored squares induce a connected subgraph of the grid graph
(`SimpleGraph.Connected`, which also makes this region nonempty, as "a single region" reads).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
A. Uejima and K. Oe, "The computational complexity of Creek puzzles on several grids", Journal
of Information Processing 28 (2020), 911-918, doi:10.2197/ipsjjip.28.911, Theorem 1.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Creek

/-- An instance: the lattice points of the board row by row, each entry `0` (no circle) or
`d + 1` (a circle with the number `d`). -/
abbrev CreekInstance := List (List ℕ)

/-- The number `m` of rows of squares. -/
def rows (i : CreekInstance) : ℕ := i.length - 1

/-- The number `n` of columns of squares. -/
def cols (i : CreekInstance) : ℕ := (i.headD []).length - 1

/-- The entry at the lattice point `(a, b)`. -/
def entry (i : CreekInstance) (a b : ℕ) : ℕ := (i.getD a []).getD b 0

/-- The grid graph on the squares: squares sharing an edge are adjacent. -/
abbrev Grid (i : CreekInstance) : SimpleGraph (Fin (rows i) × Fin (cols i)) :=
  SimpleGraph.pathGraph (rows i) □ SimpleGraph.pathGraph (cols i)

/-- The lattice point `(a, b)` touches the square `x`: it is one of the four corners of `x`. -/
def Touches (a b : ℕ) {m n : ℕ} (x : Fin m × Fin n) : Prop :=
  ((x.1 : ℕ) = a ∨ (x.1 : ℕ) + 1 = a) ∧ ((x.2 : ℕ) = b ∨ (x.2 : ℕ) + 1 = b)

instance (a b : ℕ) {m n : ℕ} (x : Fin m × Fin n) : Decidable (Touches a b x) := by
  unfold Touches; infer_instance

/-- Well-formedness: at least one row and one column of squares (two rows and two columns of
lattice points), rows of equal length, and every circle's number at most `4`. -/
def WellFormed (i : CreekInstance) : Prop :=
  2 ≤ i.length ∧ 2 ≤ (i.headD []).length ∧ (∀ row ∈ i, row.length = (i.headD []).length) ∧
    ∀ row ∈ i, ∀ e ∈ row, e ≤ 5

/-- Some set of blue squares meets every circle's number, and the uncolored squares form one
connected region. -/
def CreekFeasible (i : CreekInstance) : Prop :=
  ∃ blue : Finset (Fin (rows i) × Fin (cols i)),
    (∀ a < i.length, ∀ b < (i.headD []).length, entry i a b ≠ 0 →
      (blue.filter (Touches a b)).card = entry i a b - 1) ∧
      ((Grid i).induce {x | x ∉ blue}).Connected

open Classical in
/-- CREEK as a decision problem over bitstrings. -/
noncomputable def creekDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := CreekInstance) x with
  | some i => decide (WellFormed i ∧ CreekFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Creek
