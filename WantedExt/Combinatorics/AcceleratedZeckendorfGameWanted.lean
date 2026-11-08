/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Nat.Fib.Zeckendorf

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

/-- One turn of the Accelerated Zeckendorf Game, from state `s` to state `t`, for some
multiplicity `m > 0`: `m · C_i` (`i ≥ 2`) replaces `m` copies of each of `F_{i-1}`, `F_i` by `m`
copies of `F_{i+1}`; `m · C_1` replaces `2m` copies of `F_1` by `m` copies of `F_2`; `m · S_2`
replaces `2m` copies of `F_2` by `m` copies each of `F_1`, `F_3`; `m · S_i` (`i ≥ 3`) replaces
`2m` copies of `F_i` by `m` copies each of `F_{i-2}`, `F_{i+1}`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public def AccelZeckMove (s t : ℕ →₀ ℕ) : Prop :=
  ∃ m, 0 < m ∧
    ((∃ i, 2 ≤ i ∧ m ≤ s (i - 1) ∧ m ≤ s i ∧
        t = s - Finsupp.single (i - 1) m - Finsupp.single i m + Finsupp.single (i + 1) m) ∨
      (2 * m ≤ s 1 ∧ t = s - Finsupp.single 1 (2 * m) + Finsupp.single 2 m) ∨
      (2 * m ≤ s 2 ∧
        t = s - Finsupp.single 2 (2 * m) + Finsupp.single 1 m + Finsupp.single 3 m) ∨
      (∃ i, 3 ≤ i ∧ 2 * m ≤ s i ∧
        t = s - Finsupp.single i (2 * m) + Finsupp.single (i - 2) m +
          Finsupp.single (i + 1) m))

/-- From two copies of `F_1` the move `1 · C_1` reaches one copy of `F_2`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public theorem accelZeckMove_single_one_two :
    AccelZeckMove (Finsupp.single 1 2) (Finsupp.single 2 1) :=
  ⟨1, one_pos, Or.inr (Or.inl ⟨by simp, by simp⟩)⟩

/-- The empty state admits no move.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public theorem not_accelZeckMove_zero (t : ℕ →₀ ℕ) : ¬ AccelZeckMove 0 t := by
  rintro ⟨m, hm, ⟨i, -, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨i, -, h, -⟩⟩ <;> simp at h <;> omega

/-- A complete Accelerated Zeckendorf Game on `n` with `L` moves: the states `g 0, …, g L`
start at `n` copies of `F_1`, consecutive states are related by a move, and no move is
possible from `g L`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public def IsAccelZeckGame (n L : ℕ) (g : ℕ → ℕ →₀ ℕ) : Prop :=
  g 0 = Finsupp.single 1 n ∧ (∀ j < L, AccelZeckMove (g j) (g (j + 1))) ∧
    ∀ t, ¬ AccelZeckMove (g L) t

/-- The game on `0` is complete after no moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public theorem isAccelZeckGame_zero : IsAccelZeckGame 0 0 fun _ => 0 :=
  ⟨by simp, fun _ h => absurd h (Nat.not_lt_zero _), not_accelZeckMove_zero⟩

mutual

/-- Losing states (the player to move has no winning strategy), defined inductively together
with `AccelZeckWinning`: a state is losing when every move from it reaches a winning state. In
particular every terminal state is losing.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2 (rules (1)-(4) for winning and losing states). -/
public inductive AccelZeckLosing : (ℕ →₀ ℕ) → Prop
  | intro (s : ℕ →₀ ℕ) : (∀ t, AccelZeckMove s t → AccelZeckWinning t) → AccelZeckLosing s

/-- Winning states (the player to move has a winning strategy): some move reaches a losing
state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2 (rules (1)-(4) for winning and losing states). -/
public inductive AccelZeckWinning : (ℕ →₀ ℕ) → Prop
  | intro (s t : ℕ →₀ ℕ) : AccelZeckMove s t → AccelZeckLosing t → AccelZeckWinning s

end

/-- A state is winning iff some move from it reaches a losing state (rules (3) and (4)).

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2, rules (3)-(4). -/
public theorem accelZeckWinning_iff (s : ℕ →₀ ℕ) :
    AccelZeckWinning s ↔ ∃ t, AccelZeckMove s t ∧ AccelZeckLosing t :=
  ⟨fun ⟨_, t, h, h'⟩ => ⟨t, h, h'⟩, fun ⟨t, h, h'⟩ => .intro s t h h'⟩

/-- A state with no move is losing (rule (1)).

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2, rule (1). -/
public theorem accelZeckLosing_of_terminal {s : ℕ →₀ ℕ} (h : ∀ t, ¬ AccelZeckMove s t) :
    AccelZeckLosing s :=
  .intro s fun t ht => absurd ht (h t)

/-- The game on `2` is won by the first player, via `1 · C_1`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2 (Player 1 wins for `n = 2`). -/
public theorem accelZeckWinning_single_one_two :
    AccelZeckWinning (Finsupp.single 1 2) := by
  refine .intro _ _ accelZeckMove_single_one_two (accelZeckLosing_of_terminal ?_)
  rintro t ⟨m, hm, ⟨i, hi, h1, h2, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨i, hi, h, -⟩⟩
  · simp only [Finsupp.single_apply] at h1 h2
    split_ifs at h1 h2 <;> omega
  · simp at h; omega
  · simp at h; omega
  · simp only [Finsupp.single_apply] at h
    split_ifs at h <;> omega

/-- The Zeckendorf decomposition of `n` as a game state: one copy of `F_{j-1}` (paper
indexing) for each Mathlib index `j` in `Nat.zeckendorf n`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 1.1 and Theorem 1.3. -/
public def zeckendorfState (n : ℕ) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (((Nat.zeckendorf n).map (· - 1) : List ℕ) : Multiset ℕ)

/-- The Zeckendorf decomposition of `0` is the empty state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 1.1. -/
public theorem zeckendorfState_zero : zeckendorfState 0 = 0 := by
  simp [zeckendorfState]

/-- The Zeckendorf decomposition `4 = F_3 + F_1` (paper indexing) as a game state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 1.1. -/
public theorem zeckendorfState_four :
    zeckendorfState 4 = Finsupp.single 3 1 + Finsupp.single 1 1 := by
  have h : Nat.zeckendorf 4 = [4, 2] := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Nat.zeckendorf_succ,
      show Nat.greatestFib (3 + 1) = 4 by decide, show 3 + 1 - Nat.fib 4 = 0 + 1 by decide,
      Nat.zeckendorf_succ, show Nat.greatestFib (0 + 1) = 2 by decide,
      show 0 + 1 - Nat.fib 2 = 0 by decide, Nat.zeckendorf_zero]
  rw [zeckendorfState, h]
  clear h
  ext i
  simp only [List.map_cons, List.map_nil, Multiset.toFinsupp_apply, Multiset.coe_count,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  rcases eq_or_ne i 3 with rfl | h3
  · simp
  rcases eq_or_ne i 1 with rfl | h1
  · simp
  simp [Ne.symm h3, Ne.symm h1]

/-- Every Accelerated Zeckendorf Game terminates, at the Zeckendorf decomposition of `n`, and
any complete game on `n` has at most `((√5 + 3)/2) n - IZ(n) - ((1 + √5)/2) Z(n)` moves, where
`Z(n)` is the number of terms and `IZ(n)` the sum of the (paper) indices of the terms of the
Zeckendorf decomposition of `n`. Termination is stated as the absence of an infinite play
from `n` copies of `F_1`.

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

/-- For `n ≥ 1`, with `k` the (paper) index of the largest term of the Zeckendorf
decomposition of `n`, `k - 1` is a sharp lower bound on the length of a complete Accelerated
Zeckendorf Game on `n`: every complete game has at least `k - 1` moves and some complete game
has exactly `k - 1` moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.4. -/
public theorem_wanted accelZeckGame_sharp_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (∀ L g, IsAccelZeckGame n L g → Nat.greatestFib n - 2 ≤ L) ∧
      ∃ g, IsAccelZeckGame n (Nat.greatestFib n - 2) g

/-- For `n ≥ 1`, with `k` the (paper) index of the largest term of the Zeckendorf
decomposition of `n`, every complete Accelerated Zeckendorf Game on `n` has at least `k - 1`
moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.1. -/
public theorem_wanted accelZeckGame_lower_bound (n : ℕ) (hn : 1 ≤ n) (L : ℕ)
    (g : ℕ → ℕ →₀ ℕ) (hg : IsAccelZeckGame n L g) :
    Nat.greatestFib n - 2 ≤ L

/-- Let `p ≥ 2` and `i ≥ 1`. In a state with `F_{i-1}` copies of index `p - 1`, `F_i` copies
of index `p` and none of index `p + 1`, the move `F_{i-1} · C_p` is legal and leaves no copies
of index `p - 1`, `F_{i-2}` copies of index `p` and `F_{i-1}` copies of index `p + 1`. Paper
`F_j` is `Nat.fib (j + 1)`, including `F_0 = 1` and `F_{-1} = 0`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.2. -/
public theorem_wanted accelZeckMove_fib_combine (p i : ℕ) (hp : 2 ≤ p) (hi : 1 ≤ i)
    (s : ℕ →₀ ℕ) (h1 : s (p - 1) = Nat.fib i) (h2 : s p = Nat.fib (i + 1))
    (h3 : s (p + 1) = 0) :
    AccelZeckMove s
        (s - Finsupp.single (p - 1) (Nat.fib i) - Finsupp.single p (Nat.fib i) +
          Finsupp.single (p + 1) (Nat.fib i)) ∧
      (s - Finsupp.single (p - 1) (Nat.fib i) - Finsupp.single p (Nat.fib i) +
          Finsupp.single (p + 1) (Nat.fib i)) (p - 1) = 0 ∧
      (s - Finsupp.single (p - 1) (Nat.fib i) - Finsupp.single p (Nat.fib i) +
          Finsupp.single (p + 1) (Nat.fib i)) p = Nat.fib (i - 1) ∧
      (s - Finsupp.single (p - 1) (Nat.fib i) - Finsupp.single p (Nat.fib i) +
          Finsupp.single (p + 1) (Nat.fib i)) (p + 1) = Nat.fib i

/-- For `n = F_k` (`k ≥ 1`), `k - 1` is a sharp lower bound on the length of a complete
Accelerated Zeckendorf Game on `n`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.3. -/
public theorem_wanted accelZeckGame_sharp_lower_bound_fib (k : ℕ) (hk : 1 ≤ k) :
    (∀ L g, IsAccelZeckGame (Nat.fib (k + 1)) L g → k - 1 ≤ L) ∧
      ∃ g, IsAccelZeckGame (Nat.fib (k + 1)) (k - 1) g

/-- If the first player has a winning strategy in the Accelerated Zeckendorf Game on `n`,
exactly one first move keeps it: exactly one state reachable from `n` copies of `F_1` in one
move is losing.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Proposition 1.5. -/
public theorem_wanted accelZeck_unique_winning_first_move (n : ℕ)
    (h : AccelZeckWinning (Finsupp.single 1 n)) :
    ∃! t, AccelZeckMove (Finsupp.single 1 n) t ∧ AccelZeckLosing t

/-- Conjecture 1.7 implies Conjecture 1.6: if for every `n` such that the second player wins
the game on `n`, all states `(0, …, 0, k, 0, n - 3k)` (`k` copies of `F_3`, `n - 3k` copies of
`F_1`, `3k ≤ n`) are losing, then the first player wins the game on every `n > 9`.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.8 (with Conjectures 1.6 and 1.7). -/
public theorem_wanted accelZeck_conjecture17_implies_conjecture16
    (h17 : ∀ n, AccelZeckLosing (Finsupp.single 1 n) → ∀ k, 3 * k ≤ n →
      AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k))) :
    ∀ n, 9 < n → AccelZeckWinning (Finsupp.single 1 n)

/-- Conjecture 1.7 holds for `k ∈ {1, 2, 3, 4, 5}`: if the second player wins the game on `n`,
then for these `k` with `3k ≤ n` the state `(0, …, 0, k, 0, n - 3k)` is losing.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 1.9. -/
public theorem_wanted accelZeck_conjecture17_le_five (n : ℕ)
    (hn : AccelZeckLosing (Finsupp.single 1 n)) (k : ℕ) (hk1 : 1 ≤ k) (hk5 : k ≤ 5)
    (hkn : 3 * k ≤ n) :
    AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k))

/-- Let `k` be odd and `n ≥ 2k`, and assume every state `(0, …, 0, i, 0, n - 3i)` with `i < k`
(and `3i ≤ n`) is losing. Then `n ≥ 3k`, and `(0, …, 0, k, 0, n - 3k)` is a losing state
reachable in one move from `(0, …, 0, k, n - 2k)` (`k` copies of `F_2`, `n - 2k` of `F_1`),
and the only losing state so reachable.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.4. -/
public theorem_wanted accelZeck_odd_unique_losing_move (k n : ℕ) (hk : Odd k) (hn : 2 * k ≤ n)
    (hlose : ∀ i < k, 3 * i ≤ n →
      AccelZeckLosing (Finsupp.single 3 i + Finsupp.single 1 (n - 3 * i))) :
    3 * k ≤ n ∧
      AccelZeckMove (Finsupp.single 2 k + Finsupp.single 1 (n - 2 * k))
        (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k)) ∧
      AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k)) ∧
      ∀ t, AccelZeckMove (Finsupp.single 2 k + Finsupp.single 1 (n - 2 * k)) t →
        AccelZeckLosing t → t = Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k)

end

end MetaMathlibExt
