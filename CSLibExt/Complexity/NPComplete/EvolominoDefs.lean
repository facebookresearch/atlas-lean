/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BkVPGRecognitionDefs

/-!
# EVOLOMINO: definitions

Nikolaev (Section 2) states the problem. INSTANCE: "a rectangular board of size `p × q`, where
each cell is either white or shaded. Some of the white cells contain pre-drawn squares. The
board also includes a set of pre-drawn arrows. Each arrow starts at the center of one white cell
and ends at the center of another, traversing through the centers of intermediate white cells
horizontally, vertically or with 90 degree turns. No two arrows may pass through the same cell."
QUESTION: "Does there exist at least one solution to the puzzle, i.e., a map from the set of
white cells to the set `{∅, □}` that satisfies the rules of the puzzle: each block contains
exactly one square placed on the arrow; each arrow passes through at least two blocks; each
subsequent block in the direction of the arrow adds one square to the previous block without
rotating or flipping?" A block is "a group of squares connected vertically and horizontally"
(Nikoli's rules, quoted in Section 1). Nikolaev proves the problem NP-complete by a parsimonious
reduction from 3-SAT.

The board is given row by row: entry `c` of row `r` is `0` (white), `1` (shaded) or `2` (white
with a pre-drawn square) for cell `(r, c)`; cells outside the board count as shaded. Each arrow
is the list of its cells from start to end, a grid path of `BkVPGRecognitionDefs`
(`IsGridPath`: distinct cells, consecutive cells adjacent, `GridAdj`) of at least two white
cells; no cell lies on two arrows. A solution is the finite set `S` of cells holding squares: all
white, including every pre-drawn square. The block of a square `p` is the set of squares
reachable from `p` through orthogonally adjacent squares (`block`). Since every block holds
exactly one arrow square, the blocks met by an arrow, in the direction of the arrow, are the
blocks of the squares on the arrow in arrow order (`A.filter (· ∈ S)`); "adds one square without
rotating or flipping" says the next block has one more cell and contains a translate of the
previous one (`Evolves`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
A. V. Nikolaev, "Evolomino is NP-complete", arXiv:2503.07611 (2025), Sections 1 and 2;
puzzle rules: Nikoli Co., Ltd., "Evolomino", https://www.nikoli.co.jp/en/puzzles/evolomino/.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Evolomino

open BkVPGRecognition (GridAdj IsGridPath)

/-- An instance: the board row by row (`0` white, `1` shaded, `2` white with a pre-drawn
square), and the arrows, each the list of its cells `(row, column)` from start to end. -/
abbrev EvolominoInstance := List (List ℕ) × List (List (ℕ × ℕ))

/-- The entry of cell `p`; cells outside the board read as shaded (`1`). -/
def kind (i : EvolominoInstance) (p : ℕ × ℕ) : ℕ :=
  (i.1.getD p.1 []).getD p.2 1

/-- Well-formedness: at least one row and one column, rows of equal length, entries at most
`2`, every arrow a grid path of at least two white cells, and no cell on two arrows. -/
def WellFormed (i : EvolominoInstance) : Prop :=
  0 < i.1.length ∧ 0 < (i.1.headD []).length ∧
    (∀ row ∈ i.1, row.length = (i.1.headD []).length) ∧ (∀ row ∈ i.1, ∀ e ∈ row, e ≤ 2) ∧
    (∀ A ∈ i.2, IsGridPath A ∧ 2 ≤ A.length ∧ ∀ p ∈ A, kind i p ≠ 1) ∧ i.2.flatten.Nodup

/-- The squares `p` and `q` are equal or lie in one block of `S`: `q` is reached from `p` by
steps between orthogonally adjacent squares of `S`. Every square, even one outside `S`, is
linked to itself; for squares of `S` this is the block relation, which is how `block` and
`Solves` use it. -/
def Linked (S : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ GridAdj a b) p q

open Classical in
/-- The block of the square `p`: the squares of `S` linked to `p`. -/
noncomputable def block (S : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  S.filter (Linked S p)

/-- The block `B'` arises from the block `B` by adding one square without rotating or flipping:
it has one more cell and contains a translate of `B`. -/
def Evolves (B B' : Finset (ℕ × ℕ)) : Prop :=
  B'.card = B.card + 1 ∧
    ∃ a b : ℤ, ∀ p ∈ B, ∃ q ∈ B', (q.1 : ℤ) = p.1 + a ∧ (q.2 : ℤ) = p.2 + b

open Classical in
/-- The squares `S` solve the puzzle: they are white cells, include every pre-drawn square, every
block contains exactly one square on an arrow, every arrow has squares in at least two blocks,
and along each arrow each block evolves from the previous one. -/
def Solves (i : EvolominoInstance) (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, kind i p ≠ 1) ∧ (∀ p, kind i p = 2 → p ∈ S) ∧
    (∀ p ∈ S, ((block S p).filter fun q => ∃ A ∈ i.2, q ∈ A).card = 1) ∧
    (∀ A ∈ i.2, 2 ≤ (A.filter (· ∈ S)).length) ∧
    ∀ A ∈ i.2, ((A.filter (· ∈ S)).map (block S)).IsChain Evolves

/-- The puzzle has a solution. -/
def EvolominoFeasible (i : EvolominoInstance) : Prop :=
  ∃ S : Finset (ℕ × ℕ), Solves i S

open Classical in
/-- EVOLOMINO as a decision problem over bitstrings. -/
noncomputable def evolominoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EvolominoInstance) x with
  | some i => decide (WellFormed i ∧ EvolominoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Evolomino
