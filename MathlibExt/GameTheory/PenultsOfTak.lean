/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation
public import MathlibExt.GameTheory.SpragueGrundy
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
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

-- A line completed by two moves must contain the first move if the reply alone
-- would not complete it. Its original holes can only be the two played cells.
private theorem holes_on_completed_line {S : Finset (Fin 4 × Fin 4)} {p q : Fin 4 × Fin 4}
    (line : Fin 4 → Fin 4 × Fin 4) (coord : Fin 4 × Fin 4 → Fin 4)
    (hcoord : Function.LeftInverse coord line)
    (hfull : ∀ i, line i ∈ insert q (insert p S)) (hprev : ¬ ∀ i, line i ∈ insert q S) :
    (∃ i, line i = p) ∧ (Finset.univ.filter fun i => line i ∉ S).card ≤ 2 := by
  constructor
  · by_contra! h
    exact hprev fun i => by simpa [Finset.mem_insert, h i] using hfull i
  · suffices (Finset.univ.filter fun i => line i ∉ S) ⊆ {coord q, coord p} from
      (Finset.card_le_card this).trans Finset.card_le_two
    intro i hi
    have h := hfull i
    simp only [Finset.mem_insert, (Finset.mem_filter.mp hi).2, or_false] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton, hcoord i] using
      h.imp (congrArg coord) (congrArg coord)

private theorem holes_through_move {S : Finset (Fin 4 × Fin 4)}
    (hS : placementPenult (ticEnded 4) S) {r c : Fin 4} (hp : (r, c) ∉ S) :
    (Finset.univ.filter fun j => (r, j) ∉ S).card ≤ 2 ∨
      (Finset.univ.filter fun i => (i, c) ∉ S).card ≤ 2 := by
  obtain ⟨q, hq, hterminal⟩ := (hS.2 (r, c) hp).2
  have hprev := (hS.2 q fun h => hq (Finset.mem_insert_of_mem h)).1
  have hfull : ticEnded 4 (insert q (insert (r, c) S)) := by
    rcases hterminal with h | h
    · exact h
    · exact Or.inl ⟨0, fun j => h ▸ Finset.mem_univ _⟩
  rcases hfull with ⟨i, hi⟩ | ⟨j, hj⟩
  · obtain ⟨⟨k, hk⟩, hcard⟩ := holes_on_completed_line (fun k => (i, k)) Prod.snd
      (fun _ => rfl) hi (fun h => hprev (Or.inl (Or.inl ⟨i, h⟩)))
    obtain rfl := (Prod.mk.inj hk).1
    exact Or.inl hcard
  · obtain ⟨⟨k, hk⟩, hcard⟩ := holes_on_completed_line (fun k => (k, j)) Prod.fst
      (fun _ => rfl) hj (fun h => hprev (Or.inl (Or.inr ⟨j, h⟩)))
    obtain rfl := (Prod.mk.inj hk).2
    exact Or.inr hcard

/-- **Dual Impartial Tic penults on the 4 × 4 board have at most 9 tokens.** If $S$ is a penult of
Impartial Tic on the $4 \times 4$ board, then at most $9$ cells of the board lie outside $S$.

In the dual of Impartial Tic, tokens are removed from a full board and play ends once some row or
column is empty; its penults are the sets of empty cells of Impartial Tic penults, so this says
that a penult of the dual game on the $4 \times 4$ board has at most $9$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 4 (`integers-2025-G1-prop-4`). -/
public theorem impartialTic_dual_penult_card_le_of_four
    {S : Finset (Fin 4 × Fin 4)} (hS : placementPenult (ticEnded 4) S) :
    (Finset.univ \ S).card ≤ 9 := by
  let row (r : Fin 4) := Finset.univ.filter fun c => (r, c) ∉ S
  let col (c : Fin 4) := Finset.univ.filter fun r => (r, c) ∉ S
  have hrows : (Finset.univ \ S).card = ∑ r, (row r).card := by
    simp only [row, Finset.sdiff_eq_filter, Finset.card_filter, Fintype.sum_prod_type]
  have hcols : (Finset.univ \ S).card = ∑ c, (col c).card := by
    simp only [col, Finset.sdiff_eq_filter, Finset.card_filter, Fintype.sum_prod_type_right]
  by_cases hsmall : ∀ r, (row r).card ≤ 2
  · calc
      _ = ∑ r, (row r).card := hrows
      _ ≤ ∑ _ : Fin 4, 2 := Finset.sum_le_sum fun r _ => hsmall r
      _ ≤ 9 := by decide
  -- In a row with at least three holes, each hole lies in a column with at most two.
  -- Every other column has at most three holes since its cell in this row is occupied.
  obtain ⟨r, hr⟩ := not_forall.mp hsmall
  have hcol (c : Fin 4) : (col c).card + (if (r, c) ∉ S then 1 else 0) ≤ 3 := by
    by_cases hp : (r, c) ∉ S
    · simpa [hp] using Nat.succ_le_succ ((holes_through_move hS hp).resolve_left hr)
    · have hmiss : r ∉ col c := by simpa [col] using hp
      have hlt := Finset.card_lt_univ_of_notMem hmiss
      simpa [hp] using (Nat.le_of_lt_succ (show (col c).card < 4 from hlt))
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => hcol c
  rw [Finset.sum_add_distrib, ← hcols, ← Finset.card_filter] at hsum
  change (Finset.univ \ S).card + (row r).card ≤ _ at hsum
  simp at hsum
  omega

end

end MetaMathlibExt
