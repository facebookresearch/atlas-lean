/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.AcceleratedZeckendorfGame
public import MathlibExt.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound
public import MathlibExt.Combinatorics.AcceleratedZeckendorfGameFibonacci

/-!
# The Accelerated Zeckendorf Game

Statements from D. Garcia-Fernandezsesma, S. J. Miller, T. Rascon, R. Vandegrift and
A. Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1.

The paper indexes the Fibonacci numbers as `F_1 = 1`, `F_2 = 2`, `F_{i+1} = F_i + F_{i-1}`, so
its `F_i` is Mathlib's `Nat.fib (i + 1)` (also for the conventions `F_0 = 1`, `F_{-1} = 0` of
Lemma 2.2). A game state is a finitely supported count `s : ℕ →₀ ℕ`, `s i` being the number of
copies of `F_i` (`i ≥ 1`); the game on `n` starts at `Finsupp.single 1 n`. For `n ≥ 1` the
index `k` of the largest term of the Zeckendorf decomposition of `n` is
`Nat.greatestFib n - 1`, so the paper's `k - 1` is `Nat.greatestFib n - 2`.

Losing states are defined inductively (a state is losing when every move leads to a state
with a move to a losing state). The repository's `SpragueGrundy.ImpartialGame` is not used
because building one requires a proved termination rank, which is part of Theorem 1.3.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Accelerated Zeckendorf Game terminates at the Zeckendorf decomposition.** Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n$ be a natural
number, let $Z(n)$ be the number of terms of the Zeckendorf decomposition of $n$, and let $IZ(n)$
be the sum of the indices $k$ of its terms $F_k$. Then there is no infinite sequence of moves
starting from $n$ copies of $F_1$. Moreover, every complete Accelerated Zeckendorf Game on $n$
(a sequence of moves from $n$ copies of $F_1$ to a state from which no move is possible) ends at
the state with one copy of each term of the Zeckendorf decomposition of $n$, and its number $L$
of moves satisfies

$$L \le \frac{3 + \sqrt 5}{2} n - IZ(n) - \frac{1 + \sqrt 5}{2} Z(n).$$

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.3. -/
public theorem_wanted accelZeckGame_terminates_at_zeckendorf (n : ℕ) :
    (¬ ∃ g : ℕ → ℕ →₀ ℕ,
        g 0 = Finsupp.single 1 n ∧ ∀ j, AccelZeckMove (g j) (g (j + 1))) ∧
      ∀ L g, IsAccelZeckGame n L g →
        g L = zeckendorfState n ∧
          (L : ℝ) ≤ (Real.sqrt 5 + 3) / 2 * n - (((Nat.zeckendorf n).map (· - 1)).sum : ℕ) -
            (1 + Real.sqrt 5) / 2 * (Nat.zeckendorf n).length

/-- **Sharp lower bound on the length of an Accelerated Zeckendorf Game.** Index the Fibonacci
numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n \ge 1$ and let $F_k$ be the
largest Fibonacci number with $F_k \le n$, the largest term of the Zeckendorf decomposition of
$n$. Then every complete Accelerated Zeckendorf Game on $n$ (a sequence of moves from $n$ copies
of $F_1$ to a state from which no move is possible) has at least $k - 1$ moves, and some complete
game on $n$ has exactly $k - 1$ moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.4. -/
public theorem_wanted accelZeckGame_sharp_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (∀ L g, IsAccelZeckGame n L g → Nat.greatestFib n - 2 ≤ L) ∧
      ∃ g, IsAccelZeckGame n (Nat.greatestFib n - 2) g

/-- **Accelerated Zeckendorf Game: Conjecture 1.7 in its first five cases.** Index the Fibonacci
numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n$ be such that the state
consisting of $n$ copies of $F_1$ (the starting position of the Accelerated Zeckendorf Game on
$n$) is losing. Then for every $k$ with $1 \le k \le 5$ and $3k \le n$, the state consisting of
$k$ copies of $F_3$ and $n - 3k$ copies of $F_1$ is losing.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 1.9. -/
public theorem_wanted accelZeck_conjecture17_le_five (n : ℕ)
    (hn : AccelZeckLosing (Finsupp.single 1 n)) (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5)
    (hkn : 3 * k ≤ n) :
    AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k))

end

end MetaMathlibExt
