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

/-- **Equivalence of impartial games via their sum.** Two finite impartial games $G$ and $H$ are
equivalent if and only if their sum $G + H$ is a P-position, that is, the position of $G + H$ in
which both $G$ and $H$ are at their starting positions is a P-position.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 5 (`integers-2026-G4-lem-5`). -/
public theorem_wanted impartialGame_equiv_iff_isP_gameSum (G H : ImpartialGame) :
    Equiv G H ↔ IsP (gameSum G H) ((G.start, H.start) : (gameSum G H).Pos)

/-- **P-positions are the games of Sprague–Grundy value zero.** Let $G$ be a finite impartial game
and $n$ a natural number such that $G$ is equivalent to the Nim heap $*n$, that is, $G$ has
Sprague–Grundy value $n$. Then the starting position of $G$ is a P-position if and only if
$n = 0$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 6 (`integers-2026-G4-thm-6`). -/
public theorem_wanted isP_start_iff_of_equiv_nimHeap (G : ImpartialGame) (n : ℕ)
    (hG : Equiv G (nimHeap n)) :
    IsP G G.start ↔ n = 0

/-- **Mex rule for Sprague–Grundy values.** Let $G$ be a finite impartial game and $n$ a natural
number such that $G$ is equivalent to the Nim heap $*n$, that is, $G$ has Sprague–Grundy value
$n$. For a move from the start position of $G$ to a position $q$, write $G_q$ for the game $G$
started at $q$. Then no $G_q$ is equivalent to $*n$, and for every natural number $m < n$ some
$G_q$ is equivalent to $*m$. That is, the Sprague–Grundy value of $G$ is the mex of the
Sprague–Grundy values of the games $G_q$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Corollary 4 (`integers-2026-G4-cor-4`). -/
public theorem_wanted spragueGrundyValue_eq_mex_options (G : ImpartialGame) (n : ℕ)
    (hG : Equiv G (nimHeap n)) :
    (∀ q ∈ G.moves G.start, ¬ Equiv { G with start := q } (nimHeap n)) ∧
      ∀ m < n, ∃ q ∈ G.moves G.start, Equiv { G with start := q } (nimHeap m)

/-! ### The Princess and the Roses game -/

/-- **The Princess and the Roses game.** For $k \in \mathbb{N}$ and $p \in \mathbb{N}^k$, the
Princess and the Roses game (P&R) with $k$ labelled piles started at $p$ is the impartial game
whose positions are the $q \in \mathbb{N}^k$, with $q_i$ objects on pile $i$, and whose moves
remove one object from one nonempty pile, or one object from each of two distinct nonempty
piles. It is Slow$A$-Nim $\mathrm{SN}(k, \{1, 2\})$ started at $p$, and its rank is the total
number of objects $\sum_i q_i$.

Pile order is not normalized; the paper's convention of listing piles in non-increasing order
does not change the game.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 2.1. -/
public def princessRoses {k : ℕ} (p : Fin k → ℕ) : ImpartialGame :=
  { slowANimGame k {1, 2} with start := p }

/-- **Options in Princess and the Roses.** Let $p$ and $q$ be positions of Slow$A$-Nim on $k$
stacks with $A = \{1, 2\}$, which is the Princess and the Roses game. Then $q$ is an option of
$p$ if and only if there are stacks $i \le j$ with $p_i \ge 1$ and $p_j \ge 1$ such that
$q_l = p_l - 1$ for $l \in \{i, j\}$ and $q_l = p_l$ for every other stack $l$; that is, $q$
removes one token from stack $i$ when $i = j$, and one token from each of stacks $i$ and $j$
otherwise.

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

/-- **In two-pile Princess and the Roses, $(1, 1)$ moves to $(0, 0)$.** In the Princess and the
Roses game on two piles, $(0, 0)$ is an option of the position $(1, 1)$: one may take one object
from each pile.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 2.1. -/
public theorem zero_zero_mem_princessRoses_moves_one_one :
    ![0, 0] ∈ (princessRoses ![1, 1]).moves ![1, 1] := by
  refine mem_slowANimMoves_one_two.mpr ⟨0, 1, by decide, by decide, by decide, ?_⟩
  funext l
  fin_cases l <;> rfl

/-- **Lim's theorem on five-pile P&R.** Let $a \ge b \ge c \ge d \ge e$ be natural numbers. The
Princess and the Roses position $(a, b, c, d, e)$ is a P-position if and only if the parities of
$a, b, c, d, e$ are, in this order, (even, even, even, even, even), (odd, odd, odd, even, even),
(even, odd, odd, odd, odd) or (odd, even, even, odd, odd).

Positions with fewer piles are the cases with trailing zero piles.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 7 (`integers-2026-G4-thm-7`). -/
public theorem_wanted princessRoses_five_piles_isP_iff (a b c d e : ℕ) (hab : b ≤ a)
    (hbc : c ≤ b) (hcd : d ≤ c) (hde : e ≤ d) :
    IsP (princessRoses ![a, b, c, d, e]) (princessRoses ![a, b, c, d, e]).start ↔
      (Even a ∧ Even b ∧ Even c ∧ Even d ∧ Even e) ∨
        (Odd a ∧ Odd b ∧ Odd c ∧ Even d ∧ Even e) ∨
        (Even a ∧ Odd b ∧ Odd c ∧ Odd d ∧ Odd e) ∨
        (Odd a ∧ Even b ∧ Even c ∧ Odd d ∧ Odd e)

/-- **Sprague–Grundy values of two-pile Princess and the Roses.** For natural numbers $a \ge b$,
the Princess and the Roses position $(a, b)$ is equivalent to the Nim heap $*n$, that is, it has
Sprague–Grundy value $n$, where $n = 0$ if $a$ and $b$ are both even, $n = 1$ if $a$ is odd and
$b$ is even, $n = 2$ if $a$ and $b$ are both odd, and $n = 3$ if $a$ is even and $b$ is odd.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 8 (`integers-2026-G4-thm-8`). -/
public theorem_wanted princessRoses_two_piles_equiv_nimHeap (a b : ℕ) (hab : b ≤ a) :
    Equiv (princessRoses ![a, b])
      (nimHeap (if Even a then (if Even b then 0 else 3) else (if Even b then 1 else 2)))

/-- **Sprague–Grundy values of three-pile Princess and the Roses.** For natural numbers
$a \ge b \ge c$, the Princess and the Roses position $(a, b, c)$ is equivalent to the Nim heap
$*n$, that is, it has Sprague–Grundy value $n$, where $n = 0$ if $a$ and $b$ both have the parity
of $c$, $n = 1$ if $a$ differs from $c$ in parity and $b$ does not, $n = 2$ if $a$ and $b$ both
differ from $c$ in parity, and $n = 3$ if $b$ differs from $c$ in parity and $a$ does not.

Writing $E$ for even and $O$ for odd, the value is $0$ on $(E, E, E)$ and $(O, O, O)$, $1$ on
$(O, E, E)$ and $(E, O, O)$, $2$ on $(O, O, E)$ and $(E, E, O)$, and $3$ on $(E, O, E)$ and
$(O, E, O)$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Corollary 10 (`integers-2026-G4-cor-10`). -/
public theorem_wanted princessRoses_three_piles_equiv_nimHeap (a b c : ℕ) (hab : b ≤ a)
    (hbc : c ≤ b) :
    Equiv (princessRoses ![a, b, c])
      (nimHeap (if a % 2 = c % 2 then (if b % 2 = c % 2 then 0 else 3)
        else (if b % 2 = c % 2 then 1 else 2)))

/-- **Adding to the three largest piles of four-pile P&R.** For natural numbers
$a \ge b \ge c \ge d$ and every natural number $n$, the Princess and the Roses positions
$(a, b, c, d)$ and $(a + n, b + n, c + n, d)$ are equivalent; that is, they have the same
Sprague–Grundy value.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 9 (`integers-2026-G4-lem-9`). -/
public theorem_wanted princessRoses_four_piles_equiv_add_three_largest (a b c d n : ℕ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (princessRoses ![a + n, b + n, c + n, d])

/-! ### Simplified P&R -/

/-- **Moves of simplified P&R.** The simplified Princess and the Roses game on four sorted piles
$(a, b, c, d)$ has seven moves, given as the amounts removed from $(a, b, c, d)$: $(1, 0, 0, 0)$,
$(0, 1, 0, 0)$, $(0, 0, 0, 1)$, $(1, 1, 0, 0)$, $(1, 0, 0, 1)$, $(0, 1, 0, 1)$ and $(0, 0, 1, 1)$.

These are the moves of four-pile Princess and the Roses except taking one object from the third
pile alone or together with the first or second pile, so the third pile may be taken from only
together with the fourth.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def simplifiedPrincessRosesMoveList : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1), (1, 1, 0, 0), (1, 0, 0, 1), (0, 1, 0, 1),
    (0, 0, 1, 1)]

/-- **Options in simplified Princess and the Roses.** The seven simplified Princess and the Roses
moves are the removal vectors $(1, 0, 0, 0)$, $(0, 1, 0, 0)$, $(0, 0, 0, 1)$, $(1, 1, 0, 0)$,
$(1, 0, 0, 1)$, $(0, 1, 0, 1)$ and $(0, 0, 1, 1)$. For a quadruple $(a, b, c, d)$ of natural
numbers, its options are the quadruples $(a - r_1, b - r_2, c - r_3, d - r_4)$ for those moves
$(r_1, r_2, r_3, r_4)$ with $r_1 \le a$, $r_2 \le b$, $r_3 \le c$ and $r_4 \le d$ whose result is
in non-increasing order: $a - r_1 \ge b - r_2 \ge c - r_3 \ge d - r_4$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Sections 2.2 and 3.1. -/
public def simplifiedPrincessRosesMoves (p : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (simplifiedPrincessRosesMoveList.toFinset.filter fun m =>
      m.1 ≤ p.1 ∧ m.2.1 ≤ p.2.1 ∧ m.2.2.1 ≤ p.2.2.1 ∧ m.2.2.2 ≤ p.2.2.2 ∧
        p.2.1 - m.2.1 ≤ p.1 - m.1 ∧ p.2.2.1 - m.2.2.1 ≤ p.2.1 - m.2.1 ∧
        p.2.2.2 - m.2.2.2 ≤ p.2.2.1 - m.2.2.1).image
    fun m => (p.1 - m.1, p.2.1 - m.2.1, p.2.2.1 - m.2.2.1, p.2.2.2 - m.2.2.2)

/-- **Characterization of simplified P&R options.** For natural numbers $a, b, c, d$ and
$a', b', c', d'$, the position $[a', b', c', d']$ is an option of the simplified P&R position
$[a, b, c, d]$ if and only if $a' \le a$, $b' \le b$, $c' \le c$, $d' \le d$,
$a' \ge b' \ge c' \ge d'$, and the amounts removed $(a - a', b - b', c - c', d - d')$ form one of
the seven simplified P&R moves $(1, 0, 0, 0)$, $(0, 1, 0, 0)$, $(0, 0, 0, 1)$, $(1, 1, 0, 0)$,
$(1, 0, 0, 1)$, $(0, 1, 0, 1)$ and $(0, 0, 1, 1)$.

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

/-- **Simplified P&R moves decrease the number of objects.** For all quadruples $(a, b, c, d)$
and $(a', b', c', d')$ of natural numbers, if $(a', b', c', d')$ is an option of $(a, b, c, d)$
in simplified Princess and the Roses, then $a' + b' + c' + d' < a + b + c + d$.

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

/-- **A terminal position of simplified P&R.** In simplified Princess and the Roses, the
position $(3, 3, 3, 0)$ has no options.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem simplifiedPrincessRosesMoves_three_three_three_zero :
    simplifiedPrincessRosesMoves (3, 3, 3, 0) = ∅ := by
  decide

/-- **Simplified Princess and the Roses.** For a quadruple $p$ of natural numbers, simplified
Princess and the Roses started at $p$ is the impartial game whose positions are all quadruples
$(a, b, c, d)$ of natural numbers, whose options from a position are its simplified Princess and
the Roses options (the results of the seven simplified moves that take no pile below zero and
leave the piles in non-increasing order), whose rank is the total number of objects
$a + b + c + d$, and whose start position is $p$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def simplifiedPrincessRoses (p : ℕ × ℕ × ℕ × ℕ) : ImpartialGame where
  Pos := ℕ × ℕ × ℕ × ℕ
  eqDec := inferInstance
  moves := simplifiedPrincessRosesMoves
  rank := fun q => q.1 + q.2.1 + q.2.2.1 + q.2.2.2
  rank_lt := fun _ _ h => simplifiedPrincessRosesMoves_rank_lt h
  start := p

/-- **Four-pile P&R is equivalent to simplified P&R.** For natural numbers $a \ge b \ge c \ge d$
and every natural number $n$, the Princess and the Roses position $(a, b, c, d)$ is equivalent to
the simplified P&R position $[a + n, b + n, c + n, d]$; that is, the two have the same
Sprague–Grundy value.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Lemma 11 (`integers-2026-G4-lem-11`). -/
public theorem_wanted princessRoses_equiv_simplifiedPrincessRoses (a b c d n : ℕ)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (simplifiedPrincessRoses (a + n, b + n, c + n, d))

/-! ### The P&R Helper game -/

/-- **Moves of P&R Helper.** The list of the seven moves of P&R Helper on a position $[x, y, z]$,
each given as the triple of amounts removed from $(x, y, z)$: in order, $(1, 1, 1)$, $(1, 0, 0)$,
$(1, 2, 1)$, $(1, 1, 2)$, $(0, 1, 0)$, $(0, 1, 1)$ and $(0, 0, 1)$. As changes to the position
these are $(-1, -1, -1)$, $(-1, 0, 0)$, $(-1, -2, -1)$, $(-1, -1, -2)$, $(0, -1, 0)$,
$(0, -1, -1)$ and $(0, 0, -1)$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def princessRosesHelperMoveList : List (ℕ × ℕ × ℕ) :=
  [(1, 1, 1), (1, 0, 0), (1, 2, 1), (1, 1, 2), (0, 1, 0), (0, 1, 1), (0, 0, 1)]

/-- **Options in P&R Helper.** The P&R Helper game is played on triples of natural numbers with
the seven moves that subtract $(1, 1, 1)$, $(1, 0, 0)$, $(1, 2, 1)$, $(1, 1, 2)$, $(0, 1, 0)$,
$(0, 1, 1)$ or $(0, 0, 1)$. The options of a position $(x, y, z)$ are the triples
$(x - u, y - v, z - w)$ for those moves $(u, v, w)$ with $u \le x$, $v \le y$, $w \le z$ and
$x - u \le y - v \le z - w$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def princessRosesHelperMoves (p : ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (princessRosesHelperMoveList.toFinset.filter fun m =>
      m.1 ≤ p.1 ∧ m.2.1 ≤ p.2.1 ∧ m.2.2 ≤ p.2.2 ∧ p.1 - m.1 ≤ p.2.1 - m.2.1 ∧
        p.2.1 - m.2.1 ≤ p.2.2 - m.2.2).image
    fun m => (p.1 - m.1, p.2.1 - m.2.1, p.2.2 - m.2.2)

/-- **Characterization of P&R Helper options.** For natural numbers $x, y, z, x', y', z'$, the
position $[x', y', z']$ is an option of the P&R Helper position $[x, y, z]$ if and only if
$x' \le x$, $y' \le y$, $z' \le z$, $x' \le y' \le z'$, and the amounts removed
$(x - x', y - y', z - z')$ form one of the seven P&R Helper moves $(1, 1, 1)$, $(1, 0, 0)$,
$(1, 2, 1)$, $(1, 1, 2)$, $(0, 1, 0)$, $(0, 1, 1)$ and $(0, 0, 1)$.

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

/-- **P&R Helper moves decrease the coordinate sum.** For all triples $(x, y, z)$ and
$(x', y', z')$ of natural numbers, if $(x', y', z')$ is an option of $(x, y, z)$ in the P&R Helper
game, then $x' + y' + z' < x + y + z$.

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

/-- **Small P&R Helper positions.** In the P&R Helper game, the position $(0, 0, 0)$ has no
options, and the options of $(1, 1, 1)$ are exactly $(0, 0, 0)$ and $(0, 1, 1)$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public theorem princessRosesHelperMoves_small :
    princessRosesHelperMoves (0, 0, 0) = ∅ ∧
      princessRosesHelperMoves (1, 1, 1) = {(0, 0, 0), (0, 1, 1)} := by
  decide

/-- **The P&R Helper game.** For a triple $p$ of natural numbers, P&R Helper started at $p$ is
the impartial game whose positions are the triples $(x, y, z)$ of natural numbers, whose options
from $(x, y, z)$ are the triples $(x - u, y - v, z - w)$ for $(u, v, w)$ among $(1, 1, 1)$,
$(1, 0, 0)$, $(1, 2, 1)$, $(1, 1, 2)$, $(0, 1, 0)$, $(0, 1, 1)$ and $(0, 0, 1)$ with $u \le x$,
$v \le y$, $w \le z$ and $x - u \le y - v \le z - w$, whose rank is $x + y + z$, and which
starts at $p$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Section 3.1. -/
public def princessRosesHelper (p : ℕ × ℕ × ℕ) : ImpartialGame where
  Pos := ℕ × ℕ × ℕ
  eqDec := inferInstance
  moves := princessRosesHelperMoves
  rank := fun q => q.1 + q.2.1 + q.2.2
  rank_lt := fun _ _ h => princessRosesHelperMoves_rank_lt h
  start := p

/-- **Four-pile P&R reduces to P&R Helper.** For natural numbers $a \ge b \ge c \ge d$, the
Princess and the Roses position $(a, b, c, d)$ is equivalent to the P&R Helper position
$[d, b - c + d, a - c + d]$; that is, the two have the same Sprague–Grundy value.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 12 (`integers-2026-G4-thm-12`). -/
public theorem_wanted princessRoses_equiv_princessRosesHelper (a b c d : ℕ) (hab : b ≤ a)
    (hbc : c ≤ b) (hcd : d ≤ c) :
    Equiv (princessRoses ![a, b, c, d]) (princessRosesHelper (d, b - c + d, a - c + d))

/-! ### Theorem 13: Sprague–Grundy values of P&R Helper

The regions of `[x, y, z]` with `x ≤ y ≤ z` are `U = {z < x + y, y ≤ 2x + 1}`,
`R = {z < x + y, y > 2x + 1}`, `L = {z ≥ x + y, y ≤ 2x}` and `D = {z ≥ x + y, y > 2x}`. -/

/-- **P&R Helper positions of Sprague–Grundy value 0.** For natural numbers $x \le y \le z$,
the P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $0$ (that is,
has Sprague–Grundy value $0$) if and only if $x$, $y$ and $z$ are all even.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), first bullet. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_zero_iff (x y z : ℕ) (hxy : x ≤ y)
    (hyz : y ≤ z) :
    Equiv (princessRosesHelper (x, y, z)) (nimHeap 0) ↔ Even x ∧ Even y ∧ Even z

/-- **P&R Helper positions of Sprague–Grundy value 1 on regions U and R.** For natural numbers
$x \le y \le z$ with $z < x + y$ (the union of the regions $U$ and $R$), the P&R Helper game
started at $[x, y, z]$ is equivalent to the Nim heap of size $1$ (that is, has Sprague–Grundy
value $1$) if and only if one of the following holds: $(x, y, z) = (1, 1, 1)$; or $y = x$,
$z = x$ and $x \equiv 3 \pmod 4$; or $y = x$, $z = x + 1$, $x \equiv 1 \pmod 4$ and $x \ne 1$;
or $y = x + 1$, $z = x + 1$, $x \equiv 0 \pmod 4$ and $x \ne 0$; or $y + z - x \equiv 1 \pmod 4$
and $z > x + 1$.

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

/-- **P&R Helper positions of Sprague–Grundy value 2 on region U.** For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), write $s = y + z - x$. The
P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $2$ (that is, has
Sprague–Grundy value $2$) if and only if one of the following holds:
(a) $y = x$, $z = x$, $x \equiv 1 \pmod 4$ and $x \ne 1$;
(b) $y = x$, $z = x + 1$ and $x \equiv 3 \pmod 4$;
(c) $y = x + 1$, $z = x + 1$, $x \equiv 2 \pmod 4$ and $x \ne 2$;
(d) $y = x$, $z = x + 2$, $x \equiv 1 \pmod 4$ and $x \ne 1$;
(e) $y = x + 1$, $z = x + 2$, $x \equiv 0 \pmod 4$ and $x \ne 0$;
(f) $y = x + 2$, $z = x + 2$ and $x \equiv 3 \pmod 4$;
(g) $s \equiv 7 \pmod 8$, and either $z > x + 4$ and $y = x$, or $z > x + 5$ and $y = x + 1$,
or $z > x + 2$ and $z = x + y - 1$;
(h) $s \equiv 4 \pmod 8$, $y = x$, $x$ is odd and $z > x + 4$;
(i) $s \equiv 2 \pmod 4$, $x$, $y$, $z$ are not all even, $z > x + 2$, it is not the case that
$s \equiv 6 \pmod 8$, $z > x + 4$ and $y \le x + 1$, and it is not the case that
$s \equiv 6 \pmod 8$ and $z = x + y - 2$.

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

/-- **P&R Helper positions of Sprague–Grundy value 3 on region U.** For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), write $s = y + z - x$. The
P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $3$ (that is, has
Sprague–Grundy value $3$) if and only if one of the following holds:
(a) $(x, y, z)$ is one of $(1, 2, 2)$, $(2, 2, 3)$, $(5, 6, 6)$, $(6, 6, 7)$, $(3, 4, 5)$,
$(5, 5, 8)$;
(b) $y = x$, $z = x + 1$, $x \equiv 0 \pmod 4$ and $x \notin \{0, 4\}$;
(c) $y = x + 1$, $z = x + 1$, $x \equiv 3 \pmod 4$ and $x \notin \{3, 7\}$;
(d) $y = x + 1$, $z = x + 2$, $x \equiv 1 \pmod 4$ and $x \notin \{1, 5\}$;
(e) $s \equiv 0 \pmod 8$, $y = x$, $x$ is odd and $z > x + 5$;
(f) $s \equiv 6 \pmod 8$, $x$, $y$, $z$ are not all even, and either $z > x + 4$ and
$y \le x + 1$, or $z > x + 2$ and $z = x + y - 2$;
(g) $s \equiv 3 \pmod 4$, $z > x + 2$, it is not the case that $s \equiv 7 \pmod 8$,
$z > x + 4$ and $y \le x + 2$, and it is not the case that $s \equiv 7 \pmod 8$, $y \le 2x$
and $x + y - z \le 3$.

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

/-- **P&R Helper positions of Sprague–Grundy value 4 on region U.** For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), write $s = y + z - x$. The
P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $4$ (that is, has
Sprague–Grundy value $4$) if and only if one of the following holds:
(a) $(x, y, z)$ is one of $(2, 3, 3)$, $(5, 6, 7)$, $(4, 4, 5)$, $(7, 8, 8)$;
(b) $y = x$, $z = x + 1$, $x \equiv 2 \pmod 4$ and $x \notin \{2, 6\}$;
(c) $y = x + 1$, $z = x + 1$, $x \equiv 1 \pmod 4$ and $x \notin \{1, 5\}$;
(d) $y = x + 1$, $z = x + 2$, $x \equiv 3 \pmod 4$ and $x \notin \{3, 7\}$;
(e) $y = x + 1$, $z = x + 5$ and $x \equiv 1 \pmod 8$;
(f) $s \equiv 0 \pmod 4$, $x$, $y$, $z$ are not all even, $z > x + 2$, and none of the
following holds: $(x, y, z) = (5, 5, 8)$; $z > x + 4$, $s \equiv 4 \pmod 8$ and $y = x$;
$z > x + 5$, $s \equiv 0 \pmod 8$ and $y = x$; $y = x + 1$, $z = x + 3$, $x \equiv 0 \pmod 4$
and $x \notin \{0, 4, 8\}$; $y = x + 2$, $z = x + 3$, $x \equiv 3 \pmod 4$ and
$x \notin \{3, 7\}$; $y = x + 1$, $z = x + 5$ and $x \equiv 2 \pmod 8$; $y = x + 2$,
$z = x + 5$ and $x \equiv 1 \pmod 8$; $y = x + 1$, $z = x + 6$ and $x \equiv 1 \pmod 8$.

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

/-- **Sprague–Grundy value $5$ of P&R Helper on region $U$.** Let $x \le y \le z$ be natural
numbers with $z < x + y$ and $y \le 2x + 1$ (the region $U$). The P&R Helper position $[x, y, z]$
is equivalent to the Nim heap $*5$, that is, has Sprague–Grundy value $5$, if and only if one of
the following holds:
- $[x, y, z]$ is $[3, 4, 4]$ or $[7, 8, 9]$;
- $y = x + 1$, $z = x + 3$, $x \equiv 0 \pmod 4$ and $x \notin \{0, 4, 8\}$;
- $y = x + 2$, $z = x + 3$, $x \equiv 3 \pmod 4$ and $x \notin \{3, 7\}$;
- $y = x + 1$, $z = x + 5$ and $x \equiv 2 \pmod 8$;
- $y = x + 1$, $z = x + 6$ and $x \equiv 1 \pmod 8$;
- $y + z - x \equiv 7 \pmod 8$, $y = x + 2$, $z > x + 4$ and $x + y - z > 2$;
- $y + z - x \equiv 7 \pmod 8$, $z = x + y - 3$ and $x + 2 < y \le 2x$.

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

/-- **P&R Helper positions of Sprague–Grundy value 6 or 7 on region U.** For natural numbers
$x \le y \le z$ with $z < x + y$ and $y \le 2x + 1$ (the region $U$), the P&R Helper game started
at $[x, y, z]$ is equivalent to the Nim heap of size $6$ (that is, has Sprague–Grundy value $6$)
if and only if $y = x + 2$, $z = x + 5$ and $x \equiv 1 \pmod 8$; and it is never equivalent to
the Nim heap of size $7$.

Source: Zev Friedman, *Sprague-Grundy Values for 4-Pile Princess and the Roses*,
INTEGERS 26 (2026), Article G4, Theorem 13 (`integers-2026-G4-thm-13`), values `6` and `7`
on `U`. -/
public theorem_wanted princessRosesHelper_equiv_nimHeap_six_iff_of_mem_U (x y z : ℕ)
    (hxy : x ≤ y) (hyz : y ≤ z) (hU : z < x + y ∧ y ≤ 2 * x + 1) :
    (Equiv (princessRosesHelper (x, y, z)) (nimHeap 6) ↔
        y = x + 2 ∧ z = x + 5 ∧ x % 8 = 1) ∧
      ¬ Equiv (princessRosesHelper (x, y, z)) (nimHeap 7)

/-- **Sprague–Grundy values of P&R Helper on region R.** Let $x \le y \le z$ be natural numbers
with $z < x + y$ and $y > 2x + 1$ (the region $R$), and write $s = y + z - x$. For every natural
number $n$, the P&R Helper game started at $[x, y, z]$ is equivalent to the Nim heap of size $n$
(that is, has Sprague–Grundy value $n$) if and only if one of the following holds: $n = 0$ and
$x$, $y$, $z$ are all even; $n = 1$ and $s \equiv 1 \pmod 4$; $n = 2$, $x$ is even and $y$, $z$
are odd; $n = 3$ and $s \equiv 3 \pmod 4$; $n = 4$, $x$ is odd and $s \equiv 0 \pmod 4$;
$n = 5$, $x$ is odd and $s \equiv 2 \pmod 4$.

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

/-- **Sprague–Grundy values of P&R Helper on region L.** Let $x \le y \le z$ be natural numbers
with $z \ge x + y$ and $y \le 2x$ (the region $L$). For every natural number $n$, the P&R Helper
game started at $[x, y, z]$ is equivalent to the Nim heap of size $n$ (that is, has
Sprague–Grundy value $n$) if and only if one of the following holds: $n = 0$ and $x$, $y$, $z$
are all even; $n = 1$, $x$ and $y$ are even and $z$ is odd; $n = 2$ and
$y + 2z - 2x \equiv 3 \pmod 4$; $n = 3$ and $y + 2z - 2x \equiv 1 \pmod 4$; $n = 4$, $x$ and $z$
are odd and $y$ is even; $n = 5$, $x$ is odd and $y$ and $z$ are even.

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

/-- **Sprague–Grundy values of P&R Helper on region D.** Let $x \le y \le z$ be natural numbers
with $z \ge x + y$ and $y > 2x$ (the region $D$). For every natural number $n$, the P&R Helper
game started at $[x, y, z]$ is equivalent to the Nim heap of size $n$ (that is, has
Sprague–Grundy value $n$) if and only if $n$ is the number assigned to the parities of
$(x, y, z)$ as follows: $0$ to (even, even, even), $1$ to (even, even, odd), $2$ to
(even, odd, odd), $3$ to (even, odd, even), $4$ to (odd, even, odd), $5$ to (odd, even, even),
$6$ to (odd, odd, even) and $7$ to (odd, odd, odd).

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
