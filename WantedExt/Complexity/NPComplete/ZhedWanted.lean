/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZHED is NP-complete

Source:
S. Saha and E. D. Demaine, "ZHED is NP-complete", arXiv:2112.07914 (2021).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zhed

/-!
# ZHED is NP-complete

INSTANCE: an `n × n` grid, a target square, and numbered tiles on some other squares, each
numbered between `1` and `n - 1`.
QUESTION: is there a sequence of moves of distinct tiles that fills the target square, where a
move of a tile numbered `k` in one of the four directions fills the `k` closest unfilled squares
in that direction?

Saha and Demaine (Section 1): "An instance of this puzzle is played on a `n × n` square grid ...
One of the squares is designated as the target. Several of the other squares are filled by
tiles. Each initial tile has an integer number between `1` and `n − 1` written on it. In each
move, the player selects one of the remaining numbered tiles and a direction (up, down, left, or
right) ... If the tile was numbered `k`, the move replaces the tile with a blank tile (keeping
the square filled, but removing the number) and fills the `k` closest unfilled squares in the
specified direction with blank tiles. The objective of the game is to fill the target square."
They prove deciding whether the target can be filled NP-complete, even when every tile is
numbered `1`.

Representation. Squares are `(row, column)` pairs, `0 ≤ row, column < n`; the moves work in
`ℤ × ℤ` so that steps up and left subtract. The squares in a direction from a square, nearest
first, are those of the board along that ray; a move fills the first `k` of them that are not
yet filled, or all of them if fewer than `k` remain (the board has no squares past its edge).
Filled squares stay filled, and a selected tile loses its number, so each tile moves at most
once; the blank tiles placed by moves carry no number and never move. The board is given
explicitly, row by row, with binary numbers below `n`, so the instance has size `O(n² log n)`,
polynomial in `n`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the board, row by row (`0` for an empty square, `k ≥ 1` for a tile numbered
`k`), and the target square `(row, column)`. -/
abbrev ZhedInstance := List (List ℕ) × (ℕ × ℕ)

/-- The side length `n` of the board. -/
def size (i : ZhedInstance) : ℕ := i.1.length

/-- The entry of square `(r, c)`: `0` if empty, else the number of its tile. -/
def entry (i : ZhedInstance) (r c : ℕ) : ℕ := (i.1.getD r []).getD c 0

/-- Well-formedness: an `n × n` board with tile numbers at most `n - 1`, and a target square on
the board that holds no tile. -/
def WellFormed (i : ZhedInstance) : Prop :=
  (∀ row ∈ i.1, row.length = size i ∧ ∀ e ∈ row, e ≤ size i - 1) ∧
    i.2.1 < size i ∧ i.2.2 < size i ∧ entry i i.2.1 i.2.2 = 0

/-- Whether a square of `ℤ × ℤ` lies on the `n × n` board. -/
def onBoard (n : ℕ) (q : ℤ × ℤ) : Bool := 0 ≤ q.1 && q.1 < n && 0 ≤ q.2 && q.2 < n

/-- The four directions as unit steps `(Δrow, Δcolumn)`: up, down, left, right. -/
def dir : Fin 4 → ℤ × ℤ := ![(-1, 0), (1, 0), (0, -1), (0, 1)]

/-- The squares of the board in direction `d` from `p`, nearest first (at distances
`1, …, n`, which reach past every edge). -/
def ray (n : ℕ) (p d : ℤ × ℤ) : List (ℤ × ℤ) :=
  ((List.range n).map fun j : ℕ => (p.1 + (j + 1) * d.1, p.2 + (j + 1) * d.2)).filter
    (onBoard n)

/-- The filled squares after moving a tile at `p` numbered `k` in direction `d`, starting from
the filled squares `F`: the `k` closest unfilled squares of the ray are added. -/
def move (n : ℕ) (F : List (ℤ × ℤ)) (p : ℤ × ℤ) (k : ℕ) (d : ℤ × ℤ) : List (ℤ × ℤ) :=
  F ++ ((ray n p d).filter fun q => decide (q ∉ F)).take k

/-- The squares filled at the start: the squares of the tiles. -/
def initialFilled (i : ZhedInstance) : List (ℤ × ℤ) :=
  (List.range (size i)).flatMap fun r =>
    ((List.range (size i)).filter fun c => 0 < entry i r c).map fun c => ((r : ℤ), (c : ℤ))

/-- The filled squares after playing the moves `ms` in order; a move `((r, c), d)` moves the
tile on square `(r, c)` in direction `dir d`. -/
def play (i : ZhedInstance) (ms : List ((ℕ × ℕ) × Fin 4)) : List (ℤ × ℤ) :=
  ms.foldl (fun F m => move (size i) F ((m.1.1 : ℤ), (m.1.2 : ℤ)) (entry i m.1.1 m.1.2)
    (dir m.2)) (initialFilled i)

/-- Some sequence of moves, each selecting a different square that holds a numbered tile, fills
the target square. -/
def ZhedFeasible (i : ZhedInstance) : Prop :=
  ∃ ms : List ((ℕ × ℕ) × Fin 4), (ms.map Prod.fst).Nodup ∧
    (∀ m ∈ ms, 0 < entry i m.1.1 m.1.2) ∧ ((i.2.1 : ℤ), (i.2.2 : ℤ)) ∈ play i ms

open Classical in
/-- ZHED as a decision problem over bitstrings. -/
noncomputable def zhedDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ZhedInstance) x with
  | some i => decide (WellFormed i ∧ ZhedFeasible i)
  | none => false

/-- **ZHED is NP-complete.** Source: Saha and Demaine (2021). -/
public theorem_wanted zhed_npComplete :
    zhedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L zhedDec

end MetaMathlibExt.Complexity.NPComplete.Zhed
