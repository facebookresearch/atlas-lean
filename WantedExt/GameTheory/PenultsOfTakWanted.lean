/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.GameTheory.PenultsOfTak.WeightedCrossBound

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
