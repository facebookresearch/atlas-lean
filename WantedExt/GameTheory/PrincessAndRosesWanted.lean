/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.SpragueGrundy
public import WantedExt.Combinatorics.SlowANimWanted
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Sprague–Grundy values for Friedman's 4-pile Princess and the Roses paper

Statement-only targets from the paper, stated over
`MetaMathlibExt.SpragueGrundy.ImpartialGame`. The Sprague–Grundy value of `G` is the
paper's definition: the `n` with `G` equivalent to the Nim heap `*n` (Theorem 3, proved in
MathlibExt as `SpragueGrundy.sprague_grundy`). The game `{ G with start := q }` is the option
of `G` reached by moving to `q`.

Section 1 quotes general Sprague–Grundy facts. Sections 2–3 study the Princess and the Roses
game (P&R: remove one object from one pile, or one object from each of two piles; this is
Slow`A`-Nim `SN(k, {1, 2})` from `WantedExt.Combinatorics.SlowANimWanted`), its
"simplified P&R" restriction on four sorted piles, and the three-coordinate "P&R Helper"
game whose Sprague–Grundy values Theorem 13 classifies.
-/
namespace MetaMathlibExt

@[expose] public section

open SpragueGrundy

/-- Two finite impartial games are equivalent if and only if their sum is a P-position.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 5 (`integers-2026-G4-lem-5`). -/
public theorem_wanted impartialGame_equiv_iff_isP_gameSum (G H : ImpartialGame) :
    Equiv G H ↔ IsP (gameSum G H) ((G.start, H.start) : (gameSum G H).Pos)

/-- A finite impartial game with Sprague–Grundy value `n` (that is, equivalent to the Nim
heap `*n`) starts at a P-position if and only if `n = 0`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 6 (`integers-2026-G4-thm-6`). -/
public theorem_wanted isP_start_iff_of_equiv_nimHeap (G : ImpartialGame) (n : ℕ)
    (hG : Equiv G (nimHeap n)) :
    IsP G G.start ↔ n = 0

/-- Mex rule: if `G` has Sprague–Grundy value `n`, then no option of `G` has value `n`,
and every value `m < n` is the value of some option. That is,
`SG(G) = mex {SG(G') : G' an option of G}`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Corollary 4 (`integers-2026-G4-cor-4`). -/
public theorem_wanted spragueGrundyValue_eq_mex_options (G : ImpartialGame) (n : ℕ)
    (hG : Equiv G (nimHeap n)) :
    (∀ q ∈ G.moves G.start, ¬ Equiv { G with start := q } (nimHeap n)) ∧
      ∀ m < n, ∃ q ∈ G.moves G.start, Equiv { G with start := q } (nimHeap m)

/-! ### The Princess and the Roses game -/

/-- The Princess and the Roses (P&R) game with `k` labelled piles started at `p`: a move removes
one object from one nonempty pile, or one object from each of two nonempty piles. This is
Slow`A`-Nim `SN(k, {1, 2})` (`slowANimGame`), whose rank is the total number of objects. Pile
order is not normalized; the paper's convention of listing piles in non-increasing order does
not change the game.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 2.1. -/
public def princessRoses {k : ℕ} (p : Fin k → ℕ) : ImpartialGame :=
  { slowANimGame k {1, 2} with start := p }

/-- Characterization of P&R options: `q` is an option of `p` if and only if, for some piles
`i ≤ j` that are both nonempty in `p`, `q` takes one object from pile `i` when `i = j`, and one
object from each of piles `i` and `j` otherwise, leaving every other pile unchanged.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 2.1. -/
public theorem mem_slowANimMoves_one_two {k : ℕ} {p q : Fin k → ℕ} :
    q ∈ slowANimMoves {1, 2} p ↔
      ∃ i j : Fin k, i ≤ j ∧ 0 < p i ∧ 0 < p j ∧
        q = fun l => if l = i ∨ l = j then p l - 1 else p l := by
  simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨S, ⟨-, hcard, hp⟩, rfl⟩
    rcases hcard with h1 | h2
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      have hi := hp i (Finset.mem_singleton_self i)
      refine ⟨i, i, le_rfl, hi, hi, ?_⟩
      funext l
      simp [slowANimAfter]
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
      have hx := hp x (by simp)
      have hy := hp y (by simp)
      rcases lt_or_gt_of_ne hxy with h | h
      · refine ⟨x, y, h.le, hx, hy, ?_⟩
        funext l
        simp [slowANimAfter]
      · refine ⟨y, x, h.le, hy, hx, ?_⟩
        funext l
        simp [slowANimAfter, or_comm]
  · rintro ⟨i, j, hij, hi, hj, rfl⟩
    refine ⟨{i, j}, ⟨⟨i, by simp⟩, ?_, ?_⟩, ?_⟩
    · rcases eq_or_ne i j with rfl | h
      · simp
      · simp [Finset.card_pair h]
    · intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hi
      · rw [Finset.mem_singleton.mp hl]
        exact hj
    · funext l
      simp [slowANimAfter]

/-- From the P&R position `(1, 1)` one may take one object from each pile, reaching `(0, 0)`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 2.1. -/
public theorem zero_zero_mem_princessRoses_moves_one_one :
    ![0, 0] ∈ (princessRoses ![1, 1]).moves ![1, 1] := by
  refine mem_slowANimMoves_one_two.mpr ⟨0, 1, by decide, by decide, by decide, ?_⟩
  funext l
  fin_cases l <;> rfl

/-- Lim's theorem: a P&R position with five piles `a ≥ b ≥ c ≥ d ≥ e` is a P-position if and
only if its parity pattern is `(E, E, E, E, E)`, `(O, O, O, E, E)`, `(E, O, O, O, O)` or
`(O, E, E, O, O)`. Positions with fewer piles are the cases with trailing zero piles.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 7 (`integers-2026-G4-thm-7`). -/
public theorem_wanted princessRoses_five_piles_isP_iff (a b c d e : ℕ) (hab : b ≤ a)
    (hbc : c ≤ b) (hcd : d ≤ c) (hde : e ≤ d) :
    IsP (princessRoses ![a, b, c, d, e]) (princessRoses ![a, b, c, d, e]).start ↔
      (Even a ∧ Even b ∧ Even c ∧ Even d ∧ Even e) ∨
        (Odd a ∧ Odd b ∧ Odd c ∧ Even d ∧ Even e) ∨
        (Even a ∧ Odd b ∧ Odd c ∧ Odd d ∧ Odd e) ∨
        (Odd a ∧ Even b ∧ Even c ∧ Odd d ∧ Odd e)

/-- Two-pile P&R: for `a ≥ b`, the Sprague–Grundy value of `(a, b)` is `0, 1, 2, 3` on the
parity classes `(E, E), (O, E), (O, O), (E, O)`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 8 (`integers-2026-G4-thm-8`). -/
public theorem_wanted princessRoses_two_piles_equiv_nimHeap (a b : ℕ) (hab : b ≤ a) :
    Equiv (princessRoses ![a, b])
      (nimHeap (if Even a then (if Even b then 0 else 3) else (if Even b then 1 else 2)))

/-- Three-pile P&R: for `a ≥ b ≥ c`, the Sprague–Grundy value of `(a, b, c)` is `0` on
`(E, E, E) ∪ (O, O, O)`, `1` on `(O, E, E) ∪ (E, O, O)`, `2` on `(O, O, E) ∪ (E, E, O)` and `3`
on `(E, O, E) ∪ (O, E, O)`; each union is "`a` and `b` agree or disagree in parity with `c`".

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Corollary 10 (`integers-2026-G4-cor-10`). -/
public theorem_wanted princessRoses_three_piles_equiv_nimHeap (a b c : ℕ) (hab : b ≤ a)
    (hbc : c ≤ b) :
    Equiv (princessRoses ![a, b, c])
      (nimHeap (if a % 2 = c % 2 then (if b % 2 = c % 2 then 0 else 3)
        else (if b % 2 = c % 2 then 1 else 2)))

/-- Four-pile P&R: adding `n` objects to each of the three largest piles of
`a ≥ b ≥ c ≥ d` does not change the Sprague–Grundy value (stated as equivalence of the two
games, which is equality of Sprague–Grundy values).

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 9 (`integers-2026-G4-lem-9`). -/
public theorem_wanted princessRoses_four_piles_equiv_add_three_largest (a b c d n : ℕ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (princessRoses ![a + n, b + n, c + n, d])

/-! ### Simplified P&R -/

/-- The seven moves of simplified P&R on sorted piles `[a, b, c, d]`, as the amounts removed
from `(a, b, c, d)`: P&R moves except `(0, 0, -1, 0)`, `(-1, 0, -1, 0)` and `(0, -1, -1, 0)`, so
the third pile may be taken from only together with the fourth.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def simplifiedPrincessRosesMoveList : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1), (1, 1, 0, 0), (1, 0, 0, 1), (0, 1, 0, 1),
    (0, 0, 1, 1)]

/-- Options of a simplified P&R position `[a, b, c, d]`: a move of
`simplifiedPrincessRosesMoveList` is legal when it leaves all piles nonnegative and in
non-increasing order `a ≥ b ≥ c ≥ d`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Sections 2.2 and 3.1. -/
public def simplifiedPrincessRosesMoves (p : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (simplifiedPrincessRosesMoveList.toFinset.filter fun m =>
      m.1 ≤ p.1 ∧ m.2.1 ≤ p.2.1 ∧ m.2.2.1 ≤ p.2.2.1 ∧ m.2.2.2 ≤ p.2.2.2 ∧
        p.2.1 - m.2.1 ≤ p.1 - m.1 ∧ p.2.2.1 - m.2.2.1 ≤ p.2.1 - m.2.1 ∧
        p.2.2.2 - m.2.2.2 ≤ p.2.2.1 - m.2.2.1).image
    fun m => (p.1 - m.1, p.2.1 - m.2.1, p.2.2.1 - m.2.2.1, p.2.2.2 - m.2.2.2)

/-- Characterization of simplified P&R options: `[a', b', c', d']` is an option of
`[a, b, c, d]` if and only if no pile grows, the result is sorted `a' ≥ b' ≥ c' ≥ d'`, and the
amounts removed `(a - a', b - b', c - c', d - d')` form one of the seven moves of
`simplifiedPrincessRosesMoveList`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Sections 2.2 and 3.1. -/
public theorem mem_simplifiedPrincessRosesMoves {a b c d a' b' c' d' : ℕ} :
    (a', b', c', d') ∈ simplifiedPrincessRosesMoves (a, b, c, d) ↔
      a' ≤ a ∧ b' ≤ b ∧ c' ≤ c ∧ d' ≤ d ∧ b' ≤ a' ∧ c' ≤ b' ∧ d' ≤ c' ∧
        (a - a', b - b', c - c', d - d') ∈ simplifiedPrincessRosesMoveList := by
  simp only [simplifiedPrincessRosesMoves, Finset.mem_image, Finset.mem_filter,
    List.mem_toFinset, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨m₁, m₂, m₃, m₄, ⟨hm, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩, rfl, rfl, rfl, rfl⟩
    rw [Nat.sub_sub_self h₁, Nat.sub_sub_self h₂, Nat.sub_sub_self h₃, Nat.sub_sub_self h₄]
    exact ⟨by omega, by omega, by omega, by omega, h₅, h₆, h₇, hm⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, hm⟩
    exact ⟨a - a', b - b', c - c', d - d', ⟨hm, by omega⟩, by omega⟩

/-- Every simplified P&R move strictly decreases the total number of objects.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem simplifiedPrincessRosesMoves_rank_lt {p q : ℕ × ℕ × ℕ × ℕ}
    (h : q ∈ simplifiedPrincessRosesMoves p) :
    q.1 + q.2.1 + q.2.2.1 + q.2.2.2 < p.1 + p.2.1 + p.2.2.1 + p.2.2.2 := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨a', b', c', d'⟩ := q
  have := mem_simplifiedPrincessRosesMoves.mp h
  simp only [simplifiedPrincessRosesMoveList, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at this
  show a' + b' + c' + d' < a + b + c + d
  omega

/-- The paper's example: `[3, 3, 3, 0]` is terminal in simplified P&R.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem simplifiedPrincessRosesMoves_three_three_three_zero :
    simplifiedPrincessRosesMoves (3, 3, 3, 0) = ∅ := by
  decide

/-- Simplified P&R started at `[a, b, c, d]`; the rank is the total number of objects.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def simplifiedPrincessRoses (p : ℕ × ℕ × ℕ × ℕ) : ImpartialGame where
  Pos := ℕ × ℕ × ℕ × ℕ
  eqDec := inferInstance
  moves := simplifiedPrincessRosesMoves
  rank := fun q => q.1 + q.2.1 + q.2.2.1 + q.2.2.2
  rank_lt := fun _ _ h => simplifiedPrincessRosesMoves_rank_lt h
  start := p

/-- For `a ≥ b ≥ c ≥ d` and `n ≥ 0`, the P&R position `(a, b, c, d)` and the simplified P&R
position `[a + n, b + n, c + n, d]` have the same Sprague–Grundy value (stated as
equivalence of the two games).

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 11 (`integers-2026-G4-lem-11`). -/
public theorem_wanted princessRoses_equiv_simplifiedPrincessRoses (a b c d n : ℕ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (simplifiedPrincessRoses (a + n, b + n, c + n, d))

/-! ### The P&R Helper game -/

/-- The seven moves of P&R Helper on `[x, y, z]`, as the amounts removed from `(x, y, z)`:
`(-1, -1, -1)`, `(-1, 0, 0)`, `(-1, -2, -1)`, `(-1, -1, -2)`, `(0, -1, 0)`, `(0, -1, -1)` and
`(0, 0, -1)`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def princessRosesHelperMoveList : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 1), (1, 0, 0), (1, 2, 1), (1, 1, 2), (0, 1, 0), (0, 1, 1), (0, 0, 1)]

/-- Options of a P&R Helper position `[x, y, z]`: a move of `princessRosesHelperMoveList` is
legal when the result still satisfies `0 ≤ x ≤ y ≤ z`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def princessRosesHelperMoves (p : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (princessRosesHelperMoveList.toFinset.filter fun m =>
      m.1 ≤ p.1 ∧ m.2.1 ≤ p.2.1 ∧ m.2.2 ≤ p.2.2 ∧ p.1 - m.1 ≤ p.2.1 - m.2.1 ∧
        p.2.1 - m.2.1 ≤ p.2.2 - m.2.2).image
    fun m => (p.1 - m.1, p.2.1 - m.2.1, p.2.2 - m.2.2)

/-- Characterization of P&R Helper options: `[x', y', z']` is an option of `[x, y, z]` if and
only if no coordinate grows, the result satisfies `x' ≤ y' ≤ z'`, and the amounts removed
`(x - x', y - y', z - z')` form one of the seven moves of `princessRosesHelperMoveList`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem mem_princessRosesHelperMoves {x y z x' y' z' : ℕ} :
    (x', y', z') ∈ princessRosesHelperMoves (x, y, z) ↔
      x' ≤ x ∧ y' ≤ y ∧ z' ≤ z ∧ x' ≤ y' ∧ y' ≤ z' ∧
        (x - x', y - y', z - z') ∈ princessRosesHelperMoveList := by
  simp only [princessRosesHelperMoves, Finset.mem_image, Finset.mem_filter,
    List.mem_toFinset, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨m₁, m₂, m₃, ⟨hm, h₁, h₂, h₃, h₄, h₅⟩, rfl, rfl, rfl⟩
    rw [Nat.sub_sub_self h₁, Nat.sub_sub_self h₂, Nat.sub_sub_self h₃]
    exact ⟨by omega, by omega, by omega, h₄, h₅, hm⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, hm⟩
    exact ⟨x - x', y - y', z - z', ⟨hm, by omega⟩, by omega⟩

/-- Every P&R Helper move strictly decreases `x + y + z`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem princessRosesHelperMoves_rank_lt {p q : ℕ × ℕ × ℕ}
    (h : q ∈ princessRosesHelperMoves p) : q.1 + q.2.1 + q.2.2 < p.1 + p.2.1 + p.2.2 := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨x', y', z'⟩ := q
  have := mem_princessRosesHelperMoves.mp h
  simp only [princessRosesHelperMoveList, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at this
  show x' + y' + z' < x + y + z
  omega

/-- `[0, 0, 0]` is terminal in P&R Helper, and `[1, 1, 1]` has the options `[0, 0, 0]` and
`[0, 1, 1]`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem princessRosesHelperMoves_small :
    princessRosesHelperMoves (0, 0, 0) = ∅ ∧
      princessRosesHelperMoves (1, 1, 1) = {(0, 0, 0), (0, 1, 1)} := by
  decide

/-- P&R Helper started at `[x, y, z]`; the rank is `x + y + z`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def princessRosesHelper (p : ℕ × ℕ × ℕ) : ImpartialGame where
  Pos := ℕ × ℕ × ℕ
  eqDec := inferInstance
  moves := princessRosesHelperMoves
  rank := fun q => q.1 + q.2.1 + q.2.2
  rank_lt := fun _ _ h => princessRosesHelperMoves_rank_lt h
  start := p

/-- For `a ≥ b ≥ c ≥ d`, the P&R position `(a, b, c, d)` has the Sprague–Grundy value of the
P&R Helper position `[d, b - c + d, a - c + d]` (stated as equivalence of the two games).

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 12 (`integers-2026-G4-thm-12`). -/
public theorem_wanted princessRoses_equiv_princessRosesHelper (a b c d : ℕ) (hab : b ≤ a)
    (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (princessRosesHelper (d, b - c + d, a - c + d))

/-! ### Theorem 13: Sprague–Grundy values of P&R Helper

The regions of `[x, y, z]` with `x ≤ y ≤ z` are `U = {z < x + y, y ≤ 2x + 1}`,
`R = {z < x + y, y > 2x + 1}`, `L = {z ≥ x + y, y ≤ 2x}` and `D = {z ≥ x + y, y > 2x}`. -/

/-- A P&R Helper position `[x, y, z]` has Sprague–Grundy value `0` if and only if `x`, `y`
and `z` are all even.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), first bullet. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_zero_iff (x y z : ℕ) (hxy : x ≤ y)
    (hyz : y ≤ z) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 0) ↔ Even x ∧ Even y ∧ Even z

/-- On `U ∪ R` (that is, `z < x + y`), a P&R Helper position `[x, y, z]` has
Sprague–Grundy value `1` if and only if it is `[1, 1, 1]`, `[x, x, x]` with `x ≡ 3 (mod 4)`,
`[x, x, x + 1]` with `x ≡ 1 (mod 4)` and `x ≠ 1`, `[x, x + 1, x + 1]` with `x ≡ 0 (mod 4)` and
`x ≠ 0`, or `y + z - x ≡ 1 (mod 4)` with `z > x + 1`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), value `1` on
`U ∪ R`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_one_iff_of_lt_add (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hUR : z < x + y) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 1) ↔
      (x, y, z) = (1, 1, 1) ∨
        (y = x ∧ z = x ∧ x % 4 = 3) ∨
        (y = x ∧ z = x + 1 ∧ x % 4 = 1 ∧ x ≠ 1) ∨
        (y = x + 1 ∧ z = x + 1 ∧ x % 4 = 0 ∧ x ≠ 0) ∨
        ((y + z - x) % 4 = 1 ∧ x + 1 < z)

/-- On region `U`, the P&R Helper positions with Sprague–Grundy value `2`, as listed in the
paper.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), value `2` on `U`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_two_iff_of_mem_U (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hU : z < x + y ∧ y ≤ 2 * x + 1) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 2) ↔
      (y = x ∧ z = x ∧ x % 4 = 1 ∧ x ≠ 1) ∨
        (y = x ∧ z = x + 1 ∧ x % 4 = 3) ∨
        (y = x + 1 ∧ z = x + 1 ∧ x % 4 = 2 ∧ x ≠ 2) ∨
        (y = x ∧ z = x + 2 ∧ x % 4 = 1 ∧ x ≠ 1) ∨
        (y = x + 1 ∧ z = x + 2 ∧ x % 4 = 0 ∧ x ≠ 0) ∨
        (y = x + 2 ∧ z = x + 2 ∧ x % 4 = 3) ∨
        ((y + z - x) % 8 = 7 ∧
          ((x + 4 < z ∧ y = x) ∨ (x + 5 < z ∧ y = x + 1) ∨ (x + 2 < z ∧ z = x + y - 1))) ∨
        ((y + z - x) % 8 = 4 ∧ x = y ∧ Odd x ∧ x + 4 < z) ∨
        ((y + z - x) % 4 = 2 ∧ ¬ (Even x ∧ Even y ∧ Even z) ∧ x + 2 < z ∧
          ¬ ((y + z - x) % 8 = 6 ∧ x + 4 < z ∧ y ≤ x + 1) ∧
          ¬ ((y + z - x) % 8 = 6 ∧ z = x + y - 2))

/-- On region `U`, the P&R Helper positions with Sprague–Grundy value `3`, as listed in the
paper.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), value `3` on `U`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_three_iff_of_mem_U (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hU : z < x + y ∧ y ≤ 2 * x + 1) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 3) ↔
      (x, y, z) ∈ [(1, 2, 2), (2, 2, 3), (5, 6, 6), (6, 6, 7), (3, 4, 5), (5, 5, 8)] ∨
        (y = x ∧ z = x + 1 ∧ x % 4 = 0 ∧ x ≠ 0 ∧ x ≠ 4) ∨
        (y = x + 1 ∧ z = x + 1 ∧ x % 4 = 3 ∧ x ≠ 3 ∧ x ≠ 7) ∨
        (y = x + 1 ∧ z = x + 2 ∧ x % 4 = 1 ∧ x ≠ 1 ∧ x ≠ 5) ∨
        ((y + z - x) % 8 = 0 ∧ x = y ∧ Odd x ∧ x + 5 < z) ∨
        ((y + z - x) % 8 = 6 ∧ ¬ (Even x ∧ Even y ∧ Even z) ∧
          ((x + 4 < z ∧ y ≤ x + 1) ∨ (x + 2 < z ∧ z = x + y - 2))) ∨
        ((y + z - x) % 4 = 3 ∧ x + 2 < z ∧
          ¬ ((y + z - x) % 8 = 7 ∧ x + 4 < z ∧ y ≤ x + 2) ∧
          ¬ ((y + z - x) % 8 = 7 ∧ y ≤ 2 * x ∧ x + y - z ≤ 3))

/-- On region `U`, the P&R Helper positions with Sprague–Grundy value `4`, as listed in the
paper.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), value `4` on `U`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_four_iff_of_mem_U (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hU : z < x + y ∧ y ≤ 2 * x + 1) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 4) ↔
      (x, y, z) ∈ [(2, 3, 3), (5, 6, 7), (4, 4, 5), (7, 8, 8)] ∨
        (y = x ∧ z = x + 1 ∧ x % 4 = 2 ∧ x ≠ 2 ∧ x ≠ 6) ∨
        (y = x + 1 ∧ z = x + 1 ∧ x % 4 = 1 ∧ x ≠ 1 ∧ x ≠ 5) ∨
        (y = x + 1 ∧ z = x + 2 ∧ x % 4 = 3 ∧ x ≠ 3 ∧ x ≠ 7) ∨
        (y = x + 1 ∧ z = x + 5 ∧ x % 8 = 1) ∨
        ((y + z - x) % 4 = 0 ∧ ¬ (Even x ∧ Even y ∧ Even z) ∧ x + 2 < z ∧
          ¬ ((x, y, z) = (5, 5, 8) ∨
            (x + 4 < z ∧ (y + z - x) % 8 = 4 ∧ x = y) ∨
            (x + 5 < z ∧ (y + z - x) % 8 = 0 ∧ x = y) ∨
            (y = x + 1 ∧ z = x + 3 ∧ x % 4 = 0 ∧ x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 8) ∨
            (y = x + 2 ∧ z = x + 3 ∧ x % 4 = 3 ∧ x ≠ 3 ∧ x ≠ 7) ∨
            (y = x + 1 ∧ z = x + 5 ∧ x % 8 = 2) ∨
            (y = x + 2 ∧ z = x + 5 ∧ x % 8 = 1) ∨
            (y = x + 1 ∧ z = x + 6 ∧ x % 8 = 1)))

/-- On region `U`, the P&R Helper positions with Sprague–Grundy value `5`, as listed in the
paper.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), value `5` on `U`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_five_iff_of_mem_U (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hU : z < x + y ∧ y ≤ 2 * x + 1) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 5) ↔
      (x, y, z) ∈ [(3, 4, 4), (7, 8, 9)] ∨
        (y = x + 1 ∧ z = x + 3 ∧ x % 4 = 0 ∧ x ≠ 0 ∧ x ≠ 4 ∧ x ≠ 8) ∨
        (y = x + 2 ∧ z = x + 3 ∧ x % 4 = 3 ∧ x ≠ 3 ∧ x ≠ 7) ∨
        (y = x + 1 ∧ z = x + 5 ∧ x % 8 = 2) ∨
        (y = x + 1 ∧ z = x + 6 ∧ x % 8 = 1) ∨
        ((y + z - x) % 8 = 7 ∧ x + 4 < z ∧ y = x + 2 ∧ 2 < x + y - z) ∨
        ((y + z - x) % 8 = 7 ∧ z = x + y - 3 ∧ x + 2 < y ∧ y ≤ 2 * x)

/-- On region `U`, a P&R Helper position has Sprague–Grundy value `6` if and only if it is
`[x, x + 2, x + 5]` with `x ≡ 1 (mod 8)`, and it never has value `7`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), values `6` and `7`
on `U`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_six_iff_of_mem_U (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hU : z < x + y ∧ y ≤ 2 * x + 1) :
    (Equiv (princessRosesHelper (x, y, z)) (nimHeap 6) ↔
        y = x + 2 ∧ z = x + 5 ∧ x % 8 = 1) ∧
      ¬ Equiv (princessRosesHelper (x, y, z)) (nimHeap 7)

/-- On region `R`, the Sprague–Grundy value `n` of a P&R Helper position `[x, y, z]`:
`0` on `[E, E, E]`, `1` when `y + z - x ≡ 1 (mod 4)`, `2` on `[E, O, O]`, `3` when
`y + z - x ≡ 3 (mod 4)`, `4` when `x` is odd and `y + z - x ≡ 0 (mod 4)`, `5` when `x` is odd
and `y + z - x ≡ 2 (mod 4)`; no other value occurs.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), region `R`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_iff_of_mem_R (x y z n : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hR : z < x + y ∧ 2 * x + 1 < y) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap n) ↔
      (n = 0 ∧ Even x ∧ Even y ∧ Even z) ∨
        (n = 1 ∧ (y + z - x) % 4 = 1) ∨
        (n = 2 ∧ Even x ∧ Odd y ∧ Odd z) ∨
        (n = 3 ∧ (y + z - x) % 4 = 3) ∨
        (n = 4 ∧ Odd x ∧ (y + z - x) % 4 = 0) ∨
        (n = 5 ∧ Odd x ∧ (y + z - x) % 4 = 2)

/-- On region `L`, the Sprague–Grundy value `n` of a P&R Helper position `[x, y, z]`:
`0` on `[E, E, E]`, `1` on `[E, E, O]`, `2` when `y + 2z - 2x ≡ 3 (mod 4)`, `3` when
`y + 2z - 2x ≡ 1 (mod 4)`, `4` on `[O, E, O]`, `5` on `[O, E, E]`; no other value occurs.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), region `L`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_iff_of_mem_L (x y z n : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hL : x + y ≤ z ∧ y ≤ 2 * x) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap n) ↔
      (n = 0 ∧ Even x ∧ Even y ∧ Even z) ∨
        (n = 1 ∧ Even x ∧ Even y ∧ Odd z) ∨
        (n = 2 ∧ (y + 2 * z - 2 * x) % 4 = 3) ∨
        (n = 3 ∧ (y + 2 * z - 2 * x) % 4 = 1) ∨
        (n = 4 ∧ Odd x ∧ Even y ∧ Odd z) ∨
        (n = 5 ∧ Odd x ∧ Even y ∧ Even z)

/-- On region `D`, the Sprague–Grundy value of a P&R Helper position `[x, y, z]` is
`0, 1, …, 7` on the parity classes `[E, E, E], [E, E, O], [E, O, O], [E, O, E], [O, E, O],
[O, E, E], [O, O, E], [O, O, O]`.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), region `D`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_iff_of_mem_D (x y z n : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hD : x + y ≤ z ∧ 2 * x < y) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap n) ↔
      (n = 0 ∧ Even x ∧ Even y ∧ Even z) ∨
        (n = 1 ∧ Even x ∧ Even y ∧ Odd z) ∨
        (n = 2 ∧ Even x ∧ Odd y ∧ Odd z) ∨
        (n = 3 ∧ Even x ∧ Odd y ∧ Even z) ∨
        (n = 4 ∧ Odd x ∧ Even y ∧ Odd z) ∨
        (n = 5 ∧ Odd x ∧ Even y ∧ Even z) ∨
        (n = 6 ∧ Odd x ∧ Odd y ∧ Even z) ∨
        (n = 7 ∧ Odd x ∧ Odd y ∧ Odd z)

end

end MetaMathlibExt
