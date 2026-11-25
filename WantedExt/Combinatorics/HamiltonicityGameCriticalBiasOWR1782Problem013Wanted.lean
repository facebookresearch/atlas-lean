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

/-- **Edges of the complete graph $K_n$.** For a natural number $n$, the complete board is the
finite set of edges of the complete graph $K_n$ on the vertex set $\{0, 1, \dots, n - 1\}$, that is,
the set of all unordered pairs $\{i, j\}$ of distinct vertices $i \ne j$. -/
def completeBoard (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).edgeFinset

/-- **Free elements of a position.** For finite sets $X$ (the board), $M$ (the elements claimed
by Maker) and $R$ (the elements claimed by Breaker), the free elements are the elements of $X$
claimed by neither player, that is, the set $X \setminus (M \cup R)$. -/
def freeElems {α : Type*} [DecidableEq α] (board maker breaker : Finset α) : Finset α :=
  board \ (maker ∪ breaker)

/-- **Maker can force a win in the biased Maker-Breaker game.** Fix a finite board $X$, a bias
$b \in \mathbb{N}$ and a property of finite sets, Maker's target. At a position $(M, R)$, where
$M$ and $R$ are the sets claimed so far by Maker and by Breaker, an element of $X$ is free if it
lies in neither $M$ nor $R$. The relation "Maker, to move at $(M, R)$, can force a win" is the
least one satisfying two rules: it holds when no element of $X$ is free and $M$ satisfies the
target; and it holds when there is a free element $e$ such that, for every set $R'$ of exactly
$\min(b, r)$ of the $r$ elements that are free after $e$ is claimed, Maker can force a win at
$(M \cup \{e\}, R \cup R')$. Thus Maker claims one free element per turn, Breaker answers with
$b$ of them (all remaining ones if fewer are free), play ends when the board is exhausted, and
Maker wins if his set satisfies the target. -/
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

/-- **Maker wins the biased game with Breaker moving first.** For a finite board $X$, a bias
$b \in \mathbb{N}$ and a target property of Maker's claimed set, Maker wins the $(1 : b)$
Maker-Breaker game on $X$ in which Breaker moves first when, for every set $F \subseteq X$ of
exactly $\min(b, |X|)$ elements that Breaker may claim in his first move, Maker can force a win
when it is his turn at the position where he has claimed nothing and Breaker has claimed $F$.

Breaker moving first is the convention of both sources (Krivelevich, Section 1: "We assume that
Breaker moves first"; Chvátal-Erdős, Section 1: "with the Breaker going first"). -/
def MakerWinsBreakerFirst {α : Type*} [DecidableEq α] (board : Finset α) (b : ℕ)
    (target : Finset α → Prop) : Prop :=
  ∀ first : Finset α, first ⊆ board → first.card = min b board.card →
    MakerCanForce board b target ∅ first

/-- **Maker's Hamiltonicity target.** For a natural number $n$, a set $C$ of unordered pairs of
vertices from $\{0, 1, \dots, n - 1\}$ meets the Hamiltonicity target when the simple graph on
these $n$ vertices whose edges are the pairs of distinct vertices in $C$ is Hamiltonian: it has a
cycle passing through every vertex exactly once, with the convention that the one-vertex graph is
Hamiltonian. -/
def HamiltonianTarget (n : ℕ) (claimed : Finset (Sym2 (Fin n))) : Prop :=
  (SimpleGraph.fromEdgeSet (claimed : Set (Sym2 (Fin n)))).IsHamiltonian

/-- **The Hamiltonicity critical-bias property.** This is the statement that the critical bias of
the Hamiltonicity game is $(1 + o(1))\, n / \ln n$. In the $(1 : b)$ Maker-Breaker game on the
edges of the complete graph $K_n$ with Breaker moving first, Breaker claims $b$ free edges per
turn (all remaining free edges if fewer than $b$ are left), Maker claims one free edge per turn,
and Maker wins if, once every edge is claimed, his edges contain a Hamilton cycle. The property
says that for every real $\varepsilon > 0$ there is $n_0$ such that for every $n \ge n_0$, Maker
has a winning strategy for every natural number $b$ with $0 < b \le (1 - \varepsilon)\, n / \ln n$,
and Maker has no winning strategy for any natural number $b \ge (1 + \varepsilon)\, n / \ln n$. -/
def hamiltonicityCriticalBias : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (∀ b : ℕ, 0 < b → (b : ℝ) ≤ (1 - ε) * n / Real.log n →
      MakerWinsBreakerFirst (completeBoard n) b (HamiltonianTarget n)) ∧
    (∀ b : ℕ, (1 + ε) * n / Real.log n ≤ b →
      ¬ MakerWinsBreakerFirst (completeBoard n) b (HamiltonianTarget n))

/--
**The critical bias of the Hamiltonicity game is $(1 + o(1))\, n / \ln n$.** Consider the
$(1 : b)$ Maker-Breaker game on the edges of the complete graph $K_n$ in which Breaker moves
first: Breaker claims $b$ free edges per turn (all remaining free edges if fewer than $b$ are
left), Maker claims one free edge per turn, and Maker wins if, once every edge is claimed, his
edges contain a Hamilton cycle. For every real $\varepsilon > 0$ there is $n_0$ such that for
every $n \ge n_0$, Maker has a winning strategy for every natural number $b$ with
$0 < b \le (1 - \varepsilon)\, n / \ln n$, and Maker has no winning strategy for any natural
number $b \ge (1 + \varepsilon)\, n / \ln n$.

Maker's side is Krivelevich's Theorem 1, which gives Maker a win for every
$b \le (1 - 30 / \ln^{1/4} n)\, n / \ln n$ once $n$ is large. Breaker's side follows from the
Chvátal-Erdős Theorem 3.1, whose Breaker strategy claims every edge at some vertex for every
$b > (1 + \varepsilon / 2)\, n / \ln n$ once $n$ is large.

Source: T. Szabó (joint with H.
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
