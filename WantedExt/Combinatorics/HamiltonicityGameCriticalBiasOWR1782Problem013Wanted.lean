/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Critical bias of the Hamiltonicity Maker-Breaker game (Oberwolfach Report 1/2008)

T. Szabó (joint with H. Gebauer and M. Krivelevich), Thresholds for positional games, Oberwolfach
Report 1/2008, pp. 56-59. Open Problem 2: "Can Maker build a Hamilton cycle while playing against a
Breaker of bias `(1 - o(1)) n / ln n`?" Further open problem 1: "Close the remaining gap in Open
Problem 2." The report recalls the upper bound `(1 + ε) n / ln n` of Chvátal and Erdős for the
connectivity game and notes that the Hamiltonicity game is harder for Maker to win.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

@[expose] public section

namespace MathlibExt.Combinatorics.HamiltonicityGameCriticalBiasOWR1782Problem013Wanted

/-!
Source: T. Szabó (joint with H. Gebauer and M. Krivelevich), Thresholds for positional games, in
Combinatorics, Oberwolfach Reports 5 (2008), no. 1, pp. 56-59, DOI 10.4171/OWR/2008/01. UnsolvedMath
record UM-30000900 (`OWR-1782-013`), dataset ulamai/UnsolvedMath v1.8.0.

The `(1 : b)` Maker-Breaker game on the edges of `Kₙ` with Breaker moving first, the convention of
both resolving sources (Krivelevich, Section 1; Chvátal-Erdős, Section 1): Breaker claims `b` free
edges per turn (all remaining ones if fewer are left), Maker one, and Maker wins if his graph
contains a Hamilton cycle when the board is exhausted. `MakerCanForce` is the backward-induction
semantics of the OpenConjectures entry `EqualitiesAmongCriticalBiasesInPositionalGames`, copied
because WantedExt cannot import OpenConjectures (MathlibExt's `SetFamily.MakerBreaker` covers only
unbiased games); `MakerWinsBreakerFirst` quantifies over Breaker's first move. 'Closing the gap' is
the critical bias `(1 + o(1)) n / ln n`, stated without the bias-monotonicity lemma: for every `ε >
0` and all large `n` Maker wins for every bias `0 < b ≤ (1 - ε) n / ln n` (both sources take `b` a
positive integer) and loses for every `b ≥ (1 + ε) n / ln n`.
-/

open Filter

/-- The board of the game: the edges of the complete graph on `Fin n`. -/
def completeBoard (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).edgeFinset

/-- The elements of the board claimed by neither player. -/
def freeElems {α : Type*} [DecidableEq α] (board maker breaker : Finset α) : Finset α :=
  board \ (maker ∪ breaker)

/-- Maker, to move at the position `(maker, breaker)` of the `(1 : b)` Maker-Breaker game on
`board`, can force a win: Maker claims one free element, then Breaker claims `min b r` of the `r`
elements still free, and so on; play ends when the board is exhausted, and Maker wins if his claimed
set satisfies `target`. This is the backward-induction semantics `MakerCanForce` of the
OpenConjectures entry `EqualitiesAmongCriticalBiasesInPositionalGames`, copied here because
WantedExt cannot import OpenConjectures. -/
inductive MakerCanForce {α : Type*} [DecidableEq α] (board : Finset α) (b : ℕ)
    (target : Finset α → Prop) : Finset α → Finset α → Prop where
  | terminal (maker breaker : Finset α) (exhausted : freeElems board maker breaker = ∅)
      (won : target maker) : MakerCanForce board b target maker breaker
  | move (maker breaker : Finset α) (e : α) (free : e ∈ freeElems board maker breaker)
      (againstEveryResponse : ∀ response : Finset α,
        response ⊆ (freeElems board maker breaker).erase e →
        response.card = min b ((freeElems board maker breaker).erase e).card →
        MakerCanForce board b target (insert e maker) (breaker ∪ response)) :
      MakerCanForce board b target maker breaker

/-- Maker has a winning strategy in the `(1 : b)` game on `board` in which Breaker moves first, the
convention of both sources (Krivelevich, Section 1: "We assume that Breaker moves first";
Chvátal-Erdős, Section 1: "with the Breaker going first"): whichever `min b |board|` elements
Breaker claims in his first move, Maker can force a win from the resulting position. -/
def MakerWinsBreakerFirst {α : Type*} [DecidableEq α] (board : Finset α) (b : ℕ)
    (target : Finset α → Prop) : Prop :=
  ∀ first : Finset α, first ⊆ board → first.card = min b board.card →
    MakerCanForce board b target ∅ first

/-- Maker's goal in the Hamiltonicity game: his graph contains a Hamilton cycle. -/
def HamiltonianTarget (n : ℕ) (claimed : Finset (Sym2 (Fin n))) : Prop :=
  (SimpleGraph.fromEdgeSet (claimed : Set (Sym2 (Fin n)))).IsHamiltonian

/-- The critical bias of the `(1 : b)` Hamiltonicity game on `Kₙ` (Breaker moving first) is
`(1 + o(1)) n / ln n`: for every `ε > 0` and all large `n`, Maker wins against every positive bias
`b ≤ (1 - ε) n / ln n` and Breaker wins against every bias `b ≥ (1 + ε) n / ln n`. -/
def hamiltonicityCriticalBias : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (∀ b : ℕ, 0 < b → (b : ℝ) ≤ (1 - ε) * n / Real.log n →
      MakerWinsBreakerFirst (completeBoard n) b (HamiltonianTarget n)) ∧
    (∀ b : ℕ, (1 + ε) * n / Real.log n ≤ b →
      ¬ MakerWinsBreakerFirst (completeBoard n) b (HamiltonianTarget n))

/--
Resolved true: Krivelevich, Theorem 1: Maker has a strategy to win the `(1 : b)` Hamiltonicity game
on `Kₙ` (Breaker moving first, his Section 1) in at most `14n` moves for every `b ≤ (1 - 30 /
ln^{1/4} n) n / ln n`, for all large enough `n`; given `ε > 0`, every `b ≤ (1 - ε) n / ln n` is such
a bias once `30 / ln^{1/4} n ≤ ε`. Chvátal and Erdős, Theorem 3.1: if `ε > 0`, `n > n₀(ε)` and `b >
(1 + ε) n / log n`, then Breaker (moving first, their Section 1) has a winning strategy in the
spanning-tree game `T(n, b)`; the strategy in their proof claims every edge at some vertex, and the
report notes that the Hamiltonicity game is harder for Maker to win than the connectivity game, so
Breaker wins it for every `b ≥ (1 + ε) n / ln n` (apply Theorem 3.1 with `ε / 2`). Krivelevich's
title states the resulting critical bias `(1 + o(1)) n / ln n`. Source: T. Szabó (joint with H.
Gebauer and M. Krivelevich), Thresholds for positional games, in Combinatorics, Oberwolfach Reports
5 (2008), no. 1, pp. 56-59, DOI 10.4171/OWR/2008/01; resolution: M. Krivelevich, The critical bias
for the Hamiltonicity game is (1 + o(1)) n / ln n, J. Amer. Math. Soc. 24 (2011), 125-131, DOI
10.1090/S0894-0347-2010-00678-9, arXiv:0909.2744; V. Chvátal and P. Erdős, Biased positional games,
Ann. Discrete Math. 2 (1978), 221-229, https://users.renyi.hu/~p_erdos/1978-06.pdf, Krivelevich,
Section 1 (Breaker moves first) and Theorem 1 (Maker wins for b ≤ (1 - 30/ln^{1/4} n) n/ln n);
Chvátal-Erdős, Section 1 (Breaker moves first) and Theorem 3.1 (Breaker wins T(n, b) for b > (1 + ε)
n/log n and n > n₀(ε), by isolating a vertex); report p. 57 (the Hamiltonicity game is harder for
Maker than the connectivity game), https://arxiv.org/abs/0909.2744.
-/
public theorem_wanted hamiltonicityCriticalBias_holds : hamiltonicityCriticalBias

end MathlibExt.Combinatorics.HamiltonicityGameCriticalBiasOWR1782Problem013Wanted
