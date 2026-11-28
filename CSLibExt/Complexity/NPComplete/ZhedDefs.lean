/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ZHED: definitions

Source:
S. Saha and E. D. Demaine, "ZHED is NP-complete", arXiv:2112.07914 (2021).
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Zhed

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

end MetaMathlibExt.Complexity.NPComplete.Zhed
