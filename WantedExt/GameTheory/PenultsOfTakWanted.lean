/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.PenultsOfTak.CrossNonempty
public import MathlibExt.GameTheory.PenultsOfTak.DualPenultBound
public import MathlibExt.GameTheory.PenultsOfTak.FifthBound
public import MathlibExt.GameTheory.PenultsOfTak.LargestPenult
public import MathlibExt.GameTheory.PenultsOfTak.TicParity
public import MathlibExt.GameTheory.PenultsOfTak.VariableDiamond
public import MathlibExt.GameTheory.PenultsOfTak.WeightedCrossBound
public import MathlibExt.GameTheory.PenultsOfTakImpartialTakNotFirstPlayerWinsOfEven

namespace MetaMathlibExt

@[expose] public section

/-- **The first player wins Impartial Tak on the $5 \times 5$ board.** Impartial Tak is the
impartial placement game on the $n \times n$ board in which the players alternately place a token
on an empty cell, play ends once the tokens contain a road, and the player unable to move loses.
On the $5 \times 5$ board the first player wins from the empty board.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 3 (`integers-2025-G1-prop-3`). -/
public theorem_wanted impartialTak_five_firstPlayerWins :
    placementFirstPlayerWins takHasRoad (∅ : Finset (Fin 5 × Fin 5))

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
