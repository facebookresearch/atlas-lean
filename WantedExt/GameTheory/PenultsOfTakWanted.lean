/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Penults of Impartial Tic and Impartial Tak

Statements from Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda,
*The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1 (arXiv:2408.01837).

Both games place identical tokens on the empty cells of an `n × n` board (`Fin n × Fin n`). A
position is the finite set of occupied cells; the game has ended when the predicate `ended`
holds (Impartial Tic: some row or column is full, `ticEnded`; Impartial Tak: the tokens contain an
orthogonal path from an edge to the opposite edge, `takHasRoad`). Definition 1.1 of the paper
(terminal, ult, penult) becomes `placementTerminal`, `placementUlt`, `placementPenult`, and
normal play (the player unable to move loses) becomes `placementFirstPlayerWins`, the
negation of `SpragueGrundy.IsP` for the adapter `placementGame`. Penults of the
dual of Impartial Tic (tokens removed instead of placed) are complements of Impartial Tic
penults, so their token count is `(Finset.univ \ S).card`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.GameTheory.SpragueGrundy

namespace MetaMathlibExt

@[expose] public section

/-- **Terminal positions of a placement game.** Let $\alpha$ be a finite set of cells and let $E$
be a predicate on subsets of $\alpha$, the condition under which play has ended. A position
$S \subseteq \alpha$ (the set of occupied cells) is terminal when $E(S)$ holds or $S = \alpha$:
play has ended, or every cell is occupied. These are the positions with no options.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (terminal positions). -/
public def placementTerminal {α : Type*} [Fintype α] (ended : Finset α → Prop)
    (S : Finset α) : Prop :=
  ended S ∨ S = Finset.univ

/-- **Ults of a placement game.** Let $\alpha$ be a finite set of cells and let $E$ be a predicate
on subsets of $\alpha$, the condition under which play has ended. A position $S \subseteq \alpha$
is an ult when it is not terminal but has a terminal option: $S$ is not terminal, and there is a
cell $c \notin S$ such that $S \cup \{c\}$ is terminal.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (ults). -/
public def placementUlt {α : Type*} [Fintype α] [DecidableEq α] (ended : Finset α → Prop)
    (S : Finset α) : Prop :=
  ¬ placementTerminal ended S ∧ ∃ c ∉ S, placementTerminal ended (insert c S)

/-- **Penults of a placement game.** Let $\alpha$ be a finite set of cells and let $E$ be a
predicate on subsets of $\alpha$, the condition under which play has ended. A position
$S \subseteq \alpha$ is a penult when it is not terminal and all of its options are ults: $S$ is
not terminal, and $S \cup \{c\}$ is an ult for every cell $c \notin S$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (penults). -/
public def placementPenult {α : Type*} [Fintype α] [DecidableEq α] (ended : Finset α → Prop)
    (S : Finset α) : Prop :=
  ¬ placementTerminal ended S ∧ ∀ c ∉ S, placementUlt ended (insert c S)

/-- **The placement game.** Let $\alpha$ be a finite set of cells and let $E$ be a predicate on
subsets of $\alpha$, the condition under which play has ended. The placement game is the impartial
game whose positions are the subsets $S \subseteq \alpha$ (the occupied cells), starting from the
empty board $\emptyset$. If $E(S)$ holds there are no moves from $S$; otherwise the moves from $S$
lead to the positions $S \cup \{c\}$ with $c \notin S$. The rank of $S$ is the number
$|\alpha| - |S|$ of empty cells.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (normal-play impartial placement games). -/
public noncomputable abbrev placementGame (α : Type) [Fintype α] [DecidableEq α]
    (ended : Finset α → Prop) : SpragueGrundy.ImpartialGame where
  Pos := Finset α
  eqDec := inferInstance
  moves := fun T =>
    @ite _ (ended T) (Classical.propDecidable _) ∅ ((Finset.univ \ T).image fun c => insert c T)
  rank := fun T => Fintype.card α - T.card
  rank_lt := by
    intro p q hq
    split_ifs at hq with h
    · simp at hq
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
      have hc' : c ∉ p := (Finset.mem_sdiff.mp hc).2
      have h1 := Finset.card_insert_of_notMem hc'
      have h2 : p.card < Fintype.card α := Finset.card_lt_univ_of_notMem hc'
      omega
  start := ∅

/-- **Moves of a placement game.** Let $\alpha$ be a finite set of cells and $E$ a predicate on
subsets of $\alpha$ saying when play has ended. In the placement game on $\alpha$ with end
predicate $E$, a position $T$ is a move from a position $S$ if and only if $E(S)$ fails and
$T = S \cup \{c\}$ for some cell $c \notin S$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (normal-play impartial placement games). -/
public theorem mem_placementGame_moves {α : Type} [Fintype α] [DecidableEq α]
    (ended : Finset α → Prop) (S T : Finset α) :
    T ∈ (placementGame α ended).moves S ↔ ¬ ended S ∧ ∃ c ∉ S, insert c S = T := by
  simp only [placementGame]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **First-player win in a placement game.** Let $\alpha$ be a finite set of cells and $E$ a
predicate on subsets of $\alpha$ saying when play has ended. The player to move from a position
$S \subseteq \alpha$ wins the placement game on $\alpha$ with end predicate $E$ when $S$ is not a
P-position of that game under normal play, in which the player unable to move loses.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (normal-play impartial games) and Section 4 (winning strategies). -/
public def placementFirstPlayerWins {α : Type} [Fintype α] [DecidableEq α]
    (ended : Finset α → Prop) (S : Finset α) : Prop :=
  ¬ SpragueGrundy.IsP (placementGame α ended) S

/-- **Normal-play recursion for placement games.** Let $\alpha$ be a finite set of cells and $E$ a
predicate on subsets of $\alpha$ saying when play has ended. In the placement game on $\alpha$
with end predicate $E$, the player to move from a position $S \subseteq \alpha$ wins if and only
if $E(S)$ fails and there is a cell $c \notin S$ such that the player to move from $S \cup \{c\}$
does not win.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (normal-play impartial games). -/
public theorem placementFirstPlayerWins_iff {α : Type} [Fintype α] [DecidableEq α]
    (ended : Finset α → Prop) (S : Finset α) :
    placementFirstPlayerWins ended S ↔
      ¬ ended S ∧ ∃ c ∉ S, ¬ placementFirstPlayerWins ended (insert c S) := by
  unfold placementFirstPlayerWins
  rw [SpragueGrundy.isP_iff]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := not_forall.mp h
    obtain ⟨hq, hP⟩ := not_forall.mp hq
    obtain ⟨he, c, hc, rfl⟩ := (mem_placementGame_moves ended S q).mp hq
    exact ⟨he, c, hc, hP⟩
  · rintro ⟨he, c, hc, hP⟩ h
    exact h (insert c S) ((mem_placementGame_moves ended S _).mpr ⟨he, c, hc, rfl⟩)
      (not_not.mp hP)

/-- **The full board is terminal.** Let $\alpha$ be a finite set of cells. For every predicate $E$
on subsets of $\alpha$, the full board $\alpha$ is a terminal position of the placement game with
ending condition $E$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (a position with no options is terminal). -/
public theorem placementTerminal_univ {α : Type*} [Fintype α] (ended : Finset α → Prop) :
    placementTerminal ended Finset.univ :=
  Or.inr rfl

/-- **End of Impartial Tic.** Write the cells of the $n \times n$ board as pairs $(r, c)$ (row,
column) in $\{0, \dots, n-1\}^2$. Impartial Tic has ended at a set $S$ of occupied cells when some
row or some column is full: there is a row $r$ with $(r, c) \in S$ for every column $c$, or there
is a column $c$ with $(r, c) \in S$ for every row $r$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tic). -/
public def ticEnded (n : ℕ) (S : Finset (Fin n × Fin n)) : Prop :=
  (∃ r, ∀ c, (r, c) ∈ S) ∨ ∃ c, ∀ r, (r, c) ∈ S

/-- **Impartial Tic has not ended on the empty board.** For $n \ge 1$, play of Impartial Tic has
not ended on the empty $n \times n$ board: no row and no column is full.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tic). -/
public theorem not_ticEnded_empty {n : ℕ} (hn : 1 ≤ n) : ¬ ticEnded n ∅ := by
  rintro (⟨r, h⟩ | ⟨c, h⟩)
  · exact Finset.notMem_empty _ (h ⟨0, hn⟩)
  · exact Finset.notMem_empty _ (h ⟨0, hn⟩)

/-- **Orthogonal adjacency.** Two cells $p = (p_1, p_2)$ and $q = (q_1, q_2)$ of the $n \times n$
board $\{0, \dots, n-1\}^2$, written as (row, column), are orthogonally adjacent when they lie in
the same row and their columns differ by $1$ ($p_1 = q_1$ and $|p_2 - q_2| = 1$), or they lie in
the same column and their rows differ by $1$ ($p_2 = q_2$ and $|p_1 - q_1| = 1$).

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (orthogonal paths in Impartial Tak). -/
public def takAdjacent {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) ∨
    (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))

/-- **Roads in Impartial Tak.** Write the cells of the $n \times n$ board as pairs (row, column)
in $\{0, \dots, n-1\}^2$. Impartial Tak has ended at a set $S$ of occupied cells when the tokens
contain an orthogonal path from an edge of the board to the opposite edge: there are a token
$a \in S$ and a cell $b$ joined by a sequence $a = p_0, p_1, \dots, p_k = b$ with $k \ge 0$, in
which each $p_{i+1}$ is a token in $S$ orthogonally adjacent to $p_i$, such that $a$ lies in the
first column and $b$ in the last column, or $a$ lies in the first row and $b$ in the last row.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tak). -/
public def takHasRoad {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∃ a ∈ S, ∃ b, Relation.ReflTransGen (fun p q => takAdjacent p q ∧ q ∈ S) a b ∧
    (((a.2 : ℕ) = 0 ∧ (b.2 : ℕ) + 1 = n) ∨ ((a.1 : ℕ) = 0 ∧ (b.1 : ℕ) + 1 = n))

/-- **The empty board has no Tak road.** For every $n$, the empty $n \times n$ board contains no
road of Impartial Tak.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tak). -/
public theorem not_takHasRoad_empty {n : ℕ} : ¬ takHasRoad (∅ : Finset (Fin n × Fin n)) := by
  rintro ⟨a, ha, -⟩
  exact Finset.notMem_empty a ha

/-- **Weights of the Weighted Cross.** For natural numbers $a$ and $b$, the weight $w(a, b)$ is
$0$ if $a, b \in \{0, 4\}$; otherwise it is $2$ if $a = 2$ and $1 \le b \le 3$, or $b = 2$ and
$1 \le a \le 3$; and it is $1$ in all other cases. On the $5 \times 5$ window $0 \le a, b \le 4$
this puts weight $0$ at the four corners, $2$ on the central plus (the centre $(2, 2)$ and its
four orthogonal neighbours) and $1$ elsewhere.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Figure 10 (c) (the Weighted Cross; arXiv:2408.01837v1, Figure 7 (c)). -/
public def weightedCrossWeight (a b : ℕ) : ℕ :=
  if (a = 0 ∨ a = 4) ∧ (b = 0 ∨ b = 4) then 0
  else if (a = 2 ∧ 1 ≤ b ∧ b ≤ 3) ∨ (b = 2 ∧ 1 ≤ a ∧ a ≤ 3) then 2 else 1

/-- **Total weight of the Weighted Cross.** The weights $w(a, b)$ of the Weighted Cross over the
$5 \times 5$ window sum to $26$: $\sum_{a=0}^{4} \sum_{b=0}^{4} w(a, b) = 26$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Figure 10 (c) and Proposition 14 (coefficient `26`). -/
public theorem sum_weightedCrossWeight :
    ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, weightedCrossWeight a b = 26 := by
  decide

/-- **The first player wins Impartial Tic exactly on odd boards.** For every natural number $n$,
under normal play the first player wins Impartial Tic on the $n \times n$ board, starting from the
empty board, if and only if $n$ is odd; for even $n$ the second player wins.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 1 (`integers-2025-G1-prop-1`). -/
public theorem_wanted impartialTic_firstPlayerWins_iff_odd (n : ℕ) :
    placementFirstPlayerWins (ticEnded n) ∅ ↔ Odd n

/-- **The second player wins Impartial Tak on even boards.** Impartial Tak is the impartial
placement game on the $n \times n$ board in which the players alternately place a token on an
empty cell, play ends once the tokens contain a road, and the player unable to move loses. If $n$
is even, the first player does not win from the empty $n \times n$ board, that is, the second
player wins.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 2 (`integers-2025-G1-prop-2`). -/
public theorem_wanted impartialTak_not_firstPlayerWins_of_even {n : ℕ} (hn : Even n) :
    ¬ placementFirstPlayerWins takHasRoad (∅ : Finset (Fin n × Fin n))

/-- **The first player wins Impartial Tak on the $5 \times 5$ board.** Impartial Tak is the
impartial placement game on the $n \times n$ board in which the players alternately place a token
on an empty cell, play ends once the tokens contain a road, and the player unable to move loses.
On the $5 \times 5$ board the first player wins from the empty board.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 3 (`integers-2025-G1-prop-3`). -/
public theorem_wanted impartialTak_five_firstPlayerWins :
    placementFirstPlayerWins takHasRoad (∅ : Finset (Fin 5 × Fin 5))

/-- **Token bound for dual Impartial Tic penults.** Let $n \ge 5$. If $S$ is a penult of
Impartial Tic on the $n \times n$ board, then at most $4(n - 2)$ cells of the board lie outside
$S$.

In the dual of Impartial Tic, tokens are removed from a full board and play ends once some row or
column is empty; its penults are the sets of empty cells of Impartial Tic penults, so this says
that a penult of the dual game on the $n \times n$ board has at most $4(n - 2)$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 4 (`integers-2025-G1-prop-4`). -/
public theorem_wanted impartialTic_dual_penult_card_le {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n × Fin n)} (hS : placementPenult (ticEnded n) S) :
    (Finset.univ \ S).card ≤ 4 * (n - 2)

/-- **Dual Impartial Tic penults on the 4 × 4 board have at most 9 tokens.** If $S$ is a penult of
Impartial Tic on the $4 \times 4$ board, then at most $9$ cells of the board lie outside $S$.

In the dual of Impartial Tic, tokens are removed from a full board and play ends once some row or
column is empty; its penults are the sets of empty cells of Impartial Tic penults, so this says
that a penult of the dual game on the $4 \times 4$ board has at most $9$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 4 (`integers-2025-G1-prop-4`). -/
public theorem_wanted impartialTic_dual_penult_card_le_of_four
    {S : Finset (Fin 4 × Fin 4)} (hS : placementPenult (ticEnded 4) S) :
    (Finset.univ \ S).card ≤ 9

/-- **Token counts of dual Impartial Tic penults.** Let $n \ge 5$ and let $x$ be a natural number
with $2n \le x \le 4(n - 2)$. Then there is a penult $S$ of Impartial Tic on the $n \times n$
board such that exactly $x$ cells of the board lie outside $S$.

In the dual of Impartial Tic, tokens are removed from a full board and play ends once some row or
column is empty; its penults are the sets of empty cells of Impartial Tic penults, so this gives a
penult of the dual game on the $n \times n$ board with exactly $x$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 5 (`integers-2025-G1-prop-5`). -/
public theorem_wanted impartialTic_exists_dual_penult_card {n x : ℕ} (hn : 5 ≤ n)
    (hlo : 2 * n ≤ x) (hhi : x ≤ 4 * (n - 2)) :
    ∃ S : Finset (Fin n × Fin n), placementPenult (ticEnded n) S ∧ (Finset.univ \ S).card = x

/-- **Impartial Tak penults of every size from $n^2 - 4(n - 2) - 2$ to $n^2 - 2n$.** Impartial Tak
is the placement game on the $n \times n$ board whose play ends once the tokens contain a road. Let
$n \ge 4$ and let $x$ be a natural number with $n^2 - 4(n - 2) - 2 \le x \le n^2 - 2n$. Then there
is an Impartial Tak penult on the $n \times n$ board with exactly $x$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 6 (`integers-2025-G1-prop-6`). -/
public theorem_wanted impartialTak_exists_penult_card {n x : ℕ} (hn : 4 ≤ n)
    (hlo : n ^ 2 - 4 * (n - 2) - 2 ≤ x) (hhi : x ≤ n ^ 2 - 2 * n) :
    ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧ S.card = x

/-- **The largest Impartial Tak penult.** Impartial Tak is the placement game on the $n \times n$
board whose play ends once the tokens contain a road. For every $n \ge 2$, the largest number of
tokens in an Impartial Tak penult on the $n \times n$ board is $U(n) = n^2 - 2n$: some penult has
exactly $n^2 - 2n$ tokens and no penult has more.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Corollary 1 (`integers-2025-G1-cor-1`). -/
public theorem_wanted impartialTak_isGreatest_penult_card {n : ℕ} (hn : 2 ≤ n) :
    IsGreatest {x | ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧ S.card = x}
      (n ^ 2 - 2 * n)

/-- **Impartial Tak penults with about $n^2/3$ tokens.** Impartial Tak is the placement game on
the $n \times n$ board whose play ends once the tokens contain a road. For every $n \ge 6$ there
is an Impartial Tak penult $S$ on the $n \times n$ board whose number of tokens $|S|$ satisfies
$3|S| + 8 = n^2 + 4n$ if $n \equiv 1$ or $4 \pmod 6$, $3|S| + 12 = n^2 + 4n$ if
$n \equiv 2$ or $3 \pmod 6$, $3|S| + 16 = n^2 + 6n$ if $n \equiv 5 \pmod 6$, and
$3|S| + 18 = n^2 + 6n$ if $n \equiv 0 \pmod 6$.

That is, $|S|$ is $n^2/3 + 4n/3 - 8/3$, $n^2/3 + 4n/3 - 4$, $n^2/3 + 2n - 16/3$ and
$n^2/3 + 2n - 6$ in the four cases.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 7 (`integers-2025-G1-prop-7`). -/
public theorem_wanted impartialTak_exists_snake_penult {n : ℕ} (hn : 6 ≤ n) :
    ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧
      (n % 6 = 1 ∨ n % 6 = 4 → 3 * S.card + 8 = n ^ 2 + 4 * n) ∧
      (n % 6 = 2 ∨ n % 6 = 3 → 3 * S.card + 12 = n ^ 2 + 4 * n) ∧
      (n % 6 = 5 → 3 * S.card + 16 = n ^ 2 + 6 * n) ∧
      (n % 6 = 0 → 3 * S.card + 18 = n ^ 2 + 6 * n)

/-- **Every Cross meets an Impartial Tak penult.** Impartial Tak is the placement game on the
$n \times n$ board whose play ends once the tokens contain a road. Let $S$ be an Impartial Tak
penult on the $n \times n$ board and let $c$ be an interior cell, that is, a cell in neither the
first nor the last row and in neither the first nor the last column. Then $S$ contains $c$ or a
cell orthogonally adjacent to $c$: every Cross (an interior cell together with its four
orthogonal neighbours) contains a token.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 8 (`integers-2025-G1-prop-8`). -/
public theorem_wanted impartialTak_penult_cross_nonempty {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) (c : Fin n × Fin n) (hr : 1 ≤ (c.1 : ℕ))
    (hr' : (c.1 : ℕ) + 1 < n) (hc : 1 ≤ (c.2 : ℕ)) (hc' : (c.2 : ℕ) + 1 < n) :
    ∃ p ∈ S, p = c ∨ takAdjacent p c

/-- **An $n^2/5$ lower bound for Impartial Tak penults.** Impartial Tak is the placement game on
the $n \times n$ board whose play ends once the tokens contain a road. There is a real constant $C$
such that for every natural number $n$, every Impartial Tak penult on the $n \times n$ board has at
least $n^2/5 - Cn$ tokens; that is, every penult has at least $n^2/5 + O(n)$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 9 (`integers-2025-G1-prop-9`). -/
public theorem_wanted impartialTak_penult_card_ge_fifth :
    ∃ C : ℝ, ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), placementPenult takHasRoad S →
      (n : ℝ) ^ 2 / 5 - C * n ≤ S.card

/-- **Every Thick Cross holds three tokens of an Impartial Tak penult.** Impartial Tak is the
placement game on the $n \times n$ board whose play ends once the tokens contain a road. Index the
rows and columns by $0, \dots, n - 1$, let $S$ be an Impartial Tak penult on the $n \times n$
board, and let $r, c$ be natural numbers with $r + 4 \le n$ and $c + 4 \le n$. The Thick Cross at
$(r, c)$ is the $4 \times 4$ window of cells in rows $r, \dots, r + 3$ and columns
$c, \dots, c + 3$ with its four corners $(r, c)$, $(r, c + 3)$, $(r + 3, c)$ and
$(r + 3, c + 3)$ removed. Then at least $3$ cells of the Thick Cross belong to $S$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 11 (`integers-2025-G1-prop-11`). -/
public theorem_wanted impartialTak_penult_thickCross {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) {r c : ℕ} (hr : r + 4 ≤ n) (hc : c + 4 ≤ n) :
    3 ≤ (S.filter fun p => r ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) < r + 4 ∧ c ≤ (p.2 : ℕ) ∧
      (p.2 : ℕ) < c + 4 ∧
      ¬(((p.1 : ℕ) = r ∨ (p.1 : ℕ) = r + 3) ∧ ((p.2 : ℕ) = c ∨ (p.2 : ℕ) = c + 3))).card

/-- **An $n^2/4$ lower bound for Impartial Tak penults.** Impartial Tak is the placement game on
the $n \times n$ board whose play ends once the tokens contain a road. There is a real constant $C$
such that for every natural number $n$, every Impartial Tak penult on the $n \times n$ board has at
least $n^2/4 - Cn$ tokens; that is, every penult has at least $n^2/4 + O(n)$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 12 (`integers-2025-G1-prop-12`). -/
public theorem_wanted impartialTak_penult_card_ge_quarter :
    ∃ C : ℝ, ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), placementPenult takHasRoad S →
      (n : ℝ) ^ 2 / 4 - C * n ≤ S.card

/-- **Weighted Cross bound for Impartial Tak penults.** Let $S$ be a penult of Impartial Tak on
the $n \times n$ board, with rows and columns numbered from $0$. For all natural numbers $r, c$
with $r + 5 \le n$ and $c + 5 \le n$, consider the $5 \times 5$ window of rows $r, \dots, r + 4$
and columns $c, \dots, c + 4$, and give each token of $S$ in the window, lying in row $i$ and
column $j$ of the board, the Weighted Cross weight of position $(i - r, j - c)$. Then the tokens
of $S$ in the window have total weight at least $7$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 13 (`integers-2025-G1-prop-13`). -/
public theorem_wanted impartialTak_penult_weightedCross {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) {r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n) :
    7 ≤ ∑ p ∈ S.filter (fun p => r ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) < r + 5 ∧ c ≤ (p.2 : ℕ) ∧
      (p.2 : ℕ) < c + 5), weightedCrossWeight ((p.1 : ℕ) - r) ((p.2 : ℕ) - c)

/-- **A $\frac{7}{26}(n - 4)^2$ lower bound for Impartial Tak penults.** Impartial Tak is the
placement game on the $n \times n$ board whose play ends once the tokens contain a road. For every
$n \ge 5$, every Impartial Tak penult $S$ on the $n \times n$ board satisfies
$7(n - 4)^2 \le 26|S|$, that is, it has at least $\frac{7}{26}(n - 4)^2$ tokens.

Source: the journal text layer prints the bound as `26 (n - 4)2` with the numerator lost; the
numerator `7` is the one in arXiv:2408.01837v1, whose statement prints `(7/26)(n - 8)²` but whose
proof (summing the Weighted Cross bound of Proposition 13 over the `(n - 4)²` windows, each cell
carrying total weight at most `26`) concludes `(7/26)(n - 4)²`, matching the journal's `(n - 4)²`.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 14 (`integers-2025-G1-prop-14`). -/
public theorem_wanted impartialTak_penult_card_ge_weightedCross {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n × Fin n)} (hS : placementPenult takHasRoad S) :
    7 * (n - 4) ^ 2 ≤ 26 * S.card

end

end MetaMathlibExt
