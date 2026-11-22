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

/-- In a placement game whose play ends once `ended` holds, a position `S` is terminal when it has
no options: play has ended, or every cell is occupied.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (terminal positions). -/
public def placementTerminal {α : Type*} [Fintype α] (ended : Finset α → Prop)
    (S : Finset α) : Prop :=
  ended S ∨ S = Finset.univ

/-- A position is an ult when it is not terminal but has a terminal option.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (ults). -/
public def placementUlt {α : Type*} [Fintype α] [DecidableEq α] (ended : Finset α → Prop)
    (S : Finset α) : Prop :=
  ¬ placementTerminal ended S ∧ ∃ c ∉ S, placementTerminal ended (insert c S)

/-- A position is a penult when it is not terminal and all of its options are ults.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (penults). -/
public def placementPenult {α : Type*} [Fintype α] [DecidableEq α] (ended : Finset α → Prop)
    (S : Finset α) : Prop :=
  ¬ placementTerminal ended S ∧ ∀ c ∉ S, placementUlt ended (insert c S)

/-- The placement game as a `SpragueGrundy.ImpartialGame` on positions `Finset α`, starting from
the empty board: from a position where play has not ended, a move places one token on an empty
cell; once `ended` holds there are no moves. The rank is the number of empty cells.

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

/-- The moves of `placementGame`: place a token on an empty cell of a position where play has
not ended.

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

/-- Normal play: the player to move from `S` wins when `S` is not a P-position of
`placementGame` (`SpragueGrundy.IsP`, the player unable to move loses).

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (normal-play impartial games) and Section 4 (winning strategies). -/
public def placementFirstPlayerWins {α : Type} [Fintype α] [DecidableEq α]
    (ended : Finset α → Prop) (S : Finset α) : Prop :=
  ¬ SpragueGrundy.IsP (placementGame α ended) S

/-- The defining recursion of normal play.

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

/-- The full board is terminal.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Definition 1.1 (a position with no options is terminal). -/
public theorem placementTerminal_univ {α : Type*} [Fintype α] (ended : Finset α → Prop) :
    placementTerminal ended Finset.univ :=
  Or.inr rfl

/-- Impartial Tic has ended when some row or some column of the `n × n` board is full.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tic). -/
public def ticEnded (n : ℕ) (S : Finset (Fin n × Fin n)) : Prop :=
  (∃ r, ∀ c, (r, c) ∈ S) ∨ ∃ c, ∀ r, (r, c) ∈ S

/-- The empty `n × n` board with `n ≥ 1` has not ended in Impartial Tic.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tic). -/
public theorem not_ticEnded_empty {n : ℕ} (hn : 1 ≤ n) : ¬ ticEnded n ∅ := by
  rintro (⟨r, h⟩ | ⟨c, h⟩)
  · exact Finset.notMem_empty _ (h ⟨0, hn⟩)
  · exact Finset.notMem_empty _ (h ⟨0, hn⟩)

/-- Orthogonal adjacency of two cells of the `n × n` board.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (orthogonal paths in Impartial Tak). -/
public def takAdjacent {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) ∨
    (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))

/-- Impartial Tak has ended when the tokens contain an orthogonal path from an edge of the board
to the opposite edge: a token `a` in the first column (resp. row) joined through orthogonally
adjacent tokens to a token `b` in the last column (resp. row).

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tak). -/
public def takHasRoad {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∃ a ∈ S, ∃ b, Relation.ReflTransGen (fun p q => takAdjacent p q ∧ q ∈ S) a b ∧
    (((a.2 : ℕ) = 0 ∧ (b.2 : ℕ) + 1 = n) ∨ ((a.1 : ℕ) = 0 ∧ (b.1 : ℕ) + 1 = n))

/-- The empty board has no road.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Section 1 (rules of Impartial Tak). -/
public theorem not_takHasRoad_empty {n : ℕ} : ¬ takHasRoad (∅ : Finset (Fin n × Fin n)) := by
  rintro ⟨a, ha, -⟩
  exact Finset.notMem_empty a ha

/-- The weights of the Weighted Cross on a `5 × 5` window: `0` at the four corners, `2` on the
central plus (the centre and its four neighbours), `1` elsewhere.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Figure 10 (c) (the Weighted Cross; arXiv:2408.01837v1, Figure 7 (c)). -/
public def weightedCrossWeight (a b : ℕ) : ℕ :=
  if (a = 0 ∨ a = 4) ∧ (b = 0 ∨ b = 4) then 0
  else if (a = 2 ∧ 1 ≤ b ∧ b ≤ 3) ∨ (b = 2 ∧ 1 ≤ a ∧ a ≤ 3) then 2 else 1

/-- The Weighted Cross has total weight `26`.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Figure 10 (c) and Proposition 14 (coefficient `26`). -/
public theorem sum_weightedCrossWeight :
    ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, weightedCrossWeight a b = 26 := by
  decide

/-- Proposition 1: in Impartial Tic on an `n × n` board the first player wins exactly when `n` is
odd (for even `n` the second player wins). The mirroring strategies of the paper are not
formalized; only the outcome is stated.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 1 (`integers-2025-G1-prop-1`). -/
public theorem_wanted impartialTic_firstPlayerWins_iff_odd (n : ℕ) :
    placementFirstPlayerWins (ticEnded n) ∅ ↔ Odd n

/-- Proposition 2: in Impartial Tak on an `n × n` board with `n` even the second player wins.
The mirroring strategy of the paper is not formalized; only the outcome is stated.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 2 (`integers-2025-G1-prop-2`). -/
public theorem_wanted impartialTak_not_firstPlayerWins_of_even {n : ℕ} (hn : Even n) :
    ¬ placementFirstPlayerWins takHasRoad (∅ : Finset (Fin n × Fin n))

/-- Proposition 3: in Impartial Tak on the `5 × 5` board the first player wins. The mirroring
strategy of the paper is not formalized; only the outcome is stated.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 3 (`integers-2025-G1-prop-3`). -/
public theorem_wanted impartialTak_five_firstPlayerWins :
    placementFirstPlayerWins takHasRoad (∅ : Finset (Fin 5 × Fin 5))

/-- Proposition 4 (`n ≥ 5`): a penult of the dual of Impartial Tic on an `n × n` board has at most
`4(n - 2)` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 4 (`integers-2025-G1-prop-4`). -/
public theorem_wanted impartialTic_dual_penult_card_le {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n × Fin n)} (hS : placementPenult (ticEnded n) S) :
    (Finset.univ \ S).card ≤ 4 * (n - 2)

/-- Proposition 4 (`n = 4`): a penult of the dual of Impartial Tic on the `4 × 4` board has at
most `9` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 4 (`integers-2025-G1-prop-4`). -/
public theorem_wanted impartialTic_dual_penult_card_le_of_four
    {S : Finset (Fin 4 × Fin 4)} (hS : placementPenult (ticEnded 4) S) :
    (Finset.univ \ S).card ≤ 9

/-- Proposition 5: for `n ≥ 5` and `2n ≤ x ≤ 4(n - 2)` there is a penult of the dual of Impartial
Tic on an `n × n` board with `x` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 5 (`integers-2025-G1-prop-5`). -/
public theorem_wanted impartialTic_exists_dual_penult_card {n x : ℕ} (hn : 5 ≤ n)
    (hlo : 2 * n ≤ x) (hhi : x ≤ 4 * (n - 2)) :
    ∃ S : Finset (Fin n × Fin n), placementPenult (ticEnded n) S ∧ (Finset.univ \ S).card = x

/-- Proposition 6: for `n ≥ 4` and `n² - 4(n - 2) - 2 ≤ x ≤ n² - 2n` there is an Impartial Tak
penult on an `n × n` board with `x` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 6 (`integers-2025-G1-prop-6`). -/
public theorem_wanted impartialTak_exists_penult_card {n x : ℕ} (hn : 4 ≤ n)
    (hlo : n ^ 2 - 4 * (n - 2) - 2 ≤ x) (hhi : x ≤ n ^ 2 - 2 * n) :
    ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧ S.card = x

/-- Corollary 1: for `n ≥ 2` the largest Impartial Tak penult on an `n × n` board has
`U(n) = n² - 2n` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Corollary 1 (`integers-2025-G1-cor-1`). -/
public theorem_wanted impartialTak_isGreatest_penult_card {n : ℕ} (hn : 2 ≤ n) :
    IsGreatest {x | ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧ S.card = x}
      (n ^ 2 - 2 * n)

/-- Proposition 7: for `n ≥ 6` there is an Impartial Tak penult on an `n × n` board with
`n²/3 + 4n/3 - 8/3` tokens if `n ≡ 1, 4 (mod 6)`, `n²/3 + 4n/3 - 4` if `n ≡ 2, 3`,
`n²/3 + 2n - 16/3` if `n ≡ 5`, and `n²/3 + 2n - 6` if `n ≡ 0`; the counts are stated multiplied
by `3`.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 7 (`integers-2025-G1-prop-7`). -/
public theorem_wanted impartialTak_exists_snake_penult {n : ℕ} (hn : 6 ≤ n) :
    ∃ S : Finset (Fin n × Fin n), placementPenult takHasRoad S ∧
      (n % 6 = 1 ∨ n % 6 = 4 → 3 * S.card + 8 = n ^ 2 + 4 * n) ∧
      (n % 6 = 2 ∨ n % 6 = 3 → 3 * S.card + 12 = n ^ 2 + 4 * n) ∧
      (n % 6 = 5 → 3 * S.card + 16 = n ^ 2 + 6 * n) ∧
      (n % 6 = 0 → 3 * S.card + 18 = n ^ 2 + 6 * n)

/-- Proposition 8: in an Impartial Tak penult every Cross (an interior cell together with its four
orthogonal neighbours) contains a token.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 8 (`integers-2025-G1-prop-8`). -/
public theorem_wanted impartialTak_penult_cross_nonempty {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) (c : Fin n × Fin n) (hr : 1 ≤ (c.1 : ℕ))
    (hr' : (c.1 : ℕ) + 1 < n) (hc : 1 ≤ (c.2 : ℕ)) (hc' : (c.2 : ℕ) + 1 < n) :
    ∃ p ∈ S, p = c ∨ takAdjacent p c

/-- Proposition 9: an Impartial Tak penult on an `n × n` board has at least `n²/5 + O(n)` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 9 (`integers-2025-G1-prop-9`). -/
public theorem_wanted impartialTak_penult_card_ge_fifth :
    ∃ C : ℝ, ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), placementPenult takHasRoad S →
      (n : ℝ) ^ 2 / 5 - C * n ≤ S.card

/-- Proposition 11: in an Impartial Tak penult every Thick Cross (a `4 × 4` window without its
four corners) contains at least `3` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 11 (`integers-2025-G1-prop-11`). -/
public theorem_wanted impartialTak_penult_thickCross {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) {r c : ℕ} (hr : r + 4 ≤ n) (hc : c + 4 ≤ n) :
    3 ≤ (S.filter fun p => r ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) < r + 4 ∧ c ≤ (p.2 : ℕ) ∧
      (p.2 : ℕ) < c + 4 ∧
      ¬(((p.1 : ℕ) = r ∨ (p.1 : ℕ) = r + 3) ∧ ((p.2 : ℕ) = c ∨ (p.2 : ℕ) = c + 3))).card

/-- Proposition 12: an Impartial Tak penult on an `n × n` board has at least `n²/4 + O(n)` tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 12 (`integers-2025-G1-prop-12`). -/
public theorem_wanted impartialTak_penult_card_ge_quarter :
    ∃ C : ℝ, ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), placementPenult takHasRoad S →
      (n : ℝ) ^ 2 / 4 - C * n ≤ S.card

/-- Proposition 13: in an Impartial Tak penult the tokens of every `5 × 5` window have total
Weighted Cross weight at least `7`.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 13 (`integers-2025-G1-prop-13`). -/
public theorem_wanted impartialTak_penult_weightedCross {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) {r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n) :
    7 ≤ ∑ p ∈ S.filter (fun p => r ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) < r + 5 ∧ c ≤ (p.2 : ℕ) ∧
      (p.2 : ℕ) < c + 5), weightedCrossWeight ((p.1 : ℕ) - r) ((p.2 : ℕ) - c)

/-- Proposition 14: for `n ≥ 5` an Impartial Tak penult on an `n × n` board has at least
`(7/26)(n - 4)²` tokens, stated as `7 (n - 4)² ≤ 26 |S|`. The journal text layer prints the
bound as `26 (n - 4)2` with the numerator lost; the numerator `7` is the one in
arXiv:2408.01837v1, whose statement prints `(7/26)(n - 8)²` but whose proof (summing the Weighted
Cross bound of Proposition 13 over the `(n - 4)²` windows, each cell carrying total weight at most
`26`) concludes `(7/26)(n - 4)²`, matching the journal's `(n - 4)²`.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 14 (`integers-2025-G1-prop-14`). -/
public theorem_wanted impartialTak_penult_card_ge_weightedCross {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n × Fin n)} (hS : placementPenult takHasRoad S) :
    7 * (n - 4) ^ 2 ≤ 26 * S.card

end

end MetaMathlibExt
