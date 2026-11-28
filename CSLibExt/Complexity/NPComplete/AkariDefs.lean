/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AKARI (LIGHT UP): definitions

Source:
Brandon McPhail, "Light Up is NP-complete", unpublished manuscript, 2005.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Akari

/-- **Akari boards.** An Akari instance is a board given as a list of rows, each row a list of
natural numbers: the entry $0$ is an empty cell, $1$ is a wall, and $2 + k$ is a wall numbered $k$.
The rows need not have the same length; that is part of well-formedness. -/
abbrev AkariInstance := List (List ℕ)


/-- **Illumination on an Akari board.** Let $B$ be a board, a list of rows of natural numbers, and
write $B_{r,c}$ for the entry in row $r$ and column $c$, read as $1$ when there is no such entry. A
bulb at $(b_r, b_c)$ illuminates the cell $(r, c)$ when either $b_r = r$ and $B_{r,c'} = 0$ for
every column $c'$ strictly between $b_c$ and $c$, or $b_c = c$ and $B_{r',c} = 0$ for every row
$r'$ strictly between $b_r$ and $r$. In particular, a bulb illuminates its own cell. -/
def Illuminates (board : List (List ℕ)) (br bc r c : ℕ) : Prop :=
  (br = r ∧ ∀ cc, (min bc c < cc ∧ cc < max bc c) →
    (board.getD r []).getD cc 1 = 0) ∨
  (bc = c ∧ ∀ rr, (min br r < rr ∧ rr < max br r) →
    (board.getD rr []).getD c 1 = 0)


/-- **Well-formed Akari boards.** An Akari board is well formed when every entry is at most $6$
and all its rows have the same length. -/
def WellFormed (i : AkariInstance) : Prop :=
  ∀ row ∈ i, ∀ x ∈ row, x ≤ 6 ∧ ∀ row ∈ i, row.length = (i.getD 0 []).length

/-- **Feasible Akari boards.** Let $B$ be an Akari board with $m$ rows, let $n$ be the length of its
first row ($n = 0$ when there are no rows), and write $B_{r,c}$ for the entry in row $r$ and column
$c$, read as $1$ when there is no such entry. The board $B$ is feasible when there is a finite set
$S$ of pairs of natural numbers (the bulbs) such that every bulb $(r, c) \in S$ has $r < m$,
$c < n$ and $B_{r,c} = 0$; every cell $(r, c)$ with $r < m$, $c < n$ and $B_{r,c} = 0$ is
illuminated by some bulb in $S$; no bulb in $S$ illuminates a different bulb in $S$; and for every
$(r, c)$ with $r < m$, $c < n$ and $B_{r,c} \ge 2$, the number of bulbs $(r', c') \in S$ with
$|r - r'| + |c - c'| = 1$ equals $B_{r,c} - 2$. -/
def AkariFeasible
    (i : AkariInstance) : Prop :=
  ∃ bulbs : List (ℕ × ℕ), bulbs.Nodup ∧
    (∀ p ∈ bulbs, p.1 < i.length ∧ p.2 < (i.getD 0 []).length ∧
      (i.getD p.1 []).getD p.2 1 = 0) ∧
    (∀ r < i.length, ∀ c < (i.getD 0 []).length, (i.getD r []).getD c 1 = 0 →
      ∃ b ∈ bulbs, Illuminates i b.1 b.2 r c) ∧
    (∀ b ∈ bulbs, ∀ b' ∈ bulbs, b ≠ b' → ¬ Illuminates i b.1 b.2 b'.1 b'.2) ∧
    ∀ r < i.length, ∀ c < (i.getD 0 []).length, 2 ≤ (i.getD r []).getD c 1 →
      ((bulbs.filter (fun b => (b.1 == r + 1 && b.2 == c) || (b.1 + 1 == r && b.2 == c) ||
        (b.1 == r && b.2 == c + 1) || (b.1 == r && b.2 + 1 == c))).length =
        (i.getD r []).getD c 1 - 2)

open Classical in
/-- **The Akari decision problem.** The Akari (Light Up) decision problem accepts a list of
booleans $x$ exactly when $x$ decodes, under the canonical bitstring encoding of lists of lists of
natural numbers, to an Akari board that is well formed and feasible; it rejects every list that
does not decode. -/
noncomputable def akariDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AkariInstance) x with
  | some i => decide (WellFormed i ∧ AkariFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Akari
