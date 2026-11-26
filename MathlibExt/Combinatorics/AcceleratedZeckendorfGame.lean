/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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

/-- **Moves of the Accelerated Zeckendorf Game.** Index the Fibonacci numbers as $F_1 = 1$,
$F_2 = 2$ and $F_{i+1} = F_i + F_{i-1}$, and call a finitely supported function
$s : \mathbb{N} \to \mathbb{N}$ a state, $s(i)$ being the number of copies of $F_i$. A move
takes a state $s$ to a state $t$ if for some multiplicity $m > 0$ one of the following holds:
the move $m \cdot C_i$ with $i \ge 2$, where $s(i-1) \ge m$, $s(i) \ge m$ and $t$ is
obtained from $s$ by removing $m$ copies each of $F_{i-1}$ and $F_i$ and adding $m$ copies
of $F_{i+1}$; the move $m \cdot C_1$, where $s(1) \ge 2m$ and $t$ is obtained by replacing
$2m$ copies of $F_1$ by $m$ copies of $F_2$; the move $m \cdot S_2$, where $s(2) \ge 2m$ and
$t$ is obtained by replacing $2m$ copies of $F_2$ by $m$ copies each of $F_1$ and $F_3$; or
the move $m \cdot S_i$ with $i \ge 3$, where $s(i) \ge 2m$ and $t$ is obtained by replacing
$2m$ copies of $F_i$ by $m$ copies each of $F_{i-2}$ and $F_{i+1}$.

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

/-- **Moving a Fibonacci number of pairs in the Accelerated Zeckendorf Game.** Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{j+1} = F_j + F_{j-1}$, extended by $F_0 = 1$ and
$F_{-1} = 0$. Let $p \ge 2$ and $i \ge 1$, and let $s$ be a state with $F_{i-1}$ copies of
$F_{p-1}$, $F_i$ copies of $F_p$ and no copy of $F_{p+1}$. Let $t$ be the state obtained from $s$
by replacing $F_{i-1}$ copies of each of $F_{p-1}$ and $F_p$ by $F_{i-1}$ copies of $F_{p+1}$.
Then passing from $s$ to $t$ is a move, and $t$ has no copy of $F_{p-1}$, $F_{i-2}$ copies of
$F_p$ and $F_{i-1}$ copies of $F_{p+1}$.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.2. -/
public theorem accelZeckMove_fib_combine (p i : ℕ) (hp : 2 ≤ p) (hi : 1 ≤ i)
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
          Finsupp.single (p + 1) (Nat.fib i)) (p + 1) = Nat.fib i := by
  constructor
  · exact ⟨Nat.fib i, Nat.fib_pos.mpr hi, Or.inl
      ⟨p, hp, h1.ge, h2 ▸ Nat.fib_le_fib_succ, rfl⟩⟩
  · simp (disch := omega) [h1, h2, h3, Nat.fib_add_one (Nat.ne_of_gt hi)]

/-- **Two ones combine into a two in the Accelerated Zeckendorf Game.** Index the Fibonacci
numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Passing from the state consisting of
two copies of $F_1$ to the state consisting of one copy of $F_2$ is a move of the Accelerated
Zeckendorf Game.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public theorem accelZeckMove_single_one_two :
    AccelZeckMove (Finsupp.single 1 2) (Finsupp.single 2 1) :=
  ⟨1, one_pos, Or.inr (Or.inl ⟨by simp, by simp⟩)⟩

/-- **No move from the empty state.** No move takes the empty state (no copies of any $F_i$) to
any state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public theorem not_accelZeckMove_zero (t : ℕ →₀ ℕ) : ¬ AccelZeckMove 0 t := by
  rintro ⟨m, hm, ⟨i, -, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨i, -, h, -⟩⟩ <;> simp at h <;> omega

/-- **Complete Accelerated Zeckendorf Games.** A sequence of states $g_0, g_1, \dots$ is a
complete Accelerated Zeckendorf Game on $n$ with $L$ moves if $g_0$ consists of $n$ copies of
$F_1$, for every $j < L$ some move takes $g_j$ to $g_{j+1}$, and no move is possible from
$g_L$. The states after $g_L$ play no role.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public def IsAccelZeckGame (n L : ℕ) (g : ℕ → ℕ →₀ ℕ) : Prop :=
  g 0 = Finsupp.single 1 n ∧ (∀ j < L, AccelZeckMove (g j) (g (j + 1))) ∧
    ∀ t, ¬ AccelZeckMove (g L) t

/-- **The complete game on $0$.** The sequence whose states are all the empty state is a
complete Accelerated Zeckendorf Game on $0$ with $0$ moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Definition 1.2. -/
public theorem isAccelZeckGame_zero : IsAccelZeckGame 0 0 fun _ => 0 :=
  ⟨by simp, fun _ h => absurd h (Nat.not_lt_zero _), not_accelZeckMove_zero⟩

mutual

/-- **Losing states of the Accelerated Zeckendorf Game.** The losing and the winning states of
the Accelerated Zeckendorf Game are defined by simultaneous induction: a state is losing when
every move from it leads to a winning state, and a state is winning when some move from it leads
to a losing state. In particular every state from which no move is possible is losing.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2 (rules (1)-(4) for winning and losing states). -/
public inductive AccelZeckLosing : (ℕ →₀ ℕ) → Prop
  | intro (s : ℕ →₀ ℕ) : (∀ t, AccelZeckMove s t → AccelZeckWinning t) → AccelZeckLosing s

/-- **Winning states of the Accelerated Zeckendorf Game.** A state $s$ is winning (the player
to move has a winning strategy) if some move takes $s$ to a losing state. Winning and losing
states are defined by simultaneous induction: a state is losing if every move from it reaches
a winning state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2 (rules (1)-(4) for winning and losing states). -/
public inductive AccelZeckWinning : (ℕ →₀ ℕ) → Prop
  | intro (s t : ℕ →₀ ℕ) : AccelZeckMove s t → AccelZeckLosing t → AccelZeckWinning s

end

/-- **Characterization of winning states.** A state $s$ is winning if and only if some move
takes $s$ to a losing state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2, rules (3)-(4). -/
public theorem accelZeckWinning_iff (s : ℕ →₀ ℕ) :
    AccelZeckWinning s ↔ ∃ t, AccelZeckMove s t ∧ AccelZeckLosing t :=
  ⟨fun ⟨_, t, h, h'⟩ => ⟨t, h, h'⟩, fun ⟨t, h, h'⟩ => .intro s t h h'⟩

/-- **Terminal states are losing in the Accelerated Zeckendorf Game.** Every state of the
Accelerated Zeckendorf Game from which no move is possible is a losing state.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 2.2, rule (1). -/
public theorem accelZeckLosing_of_terminal {s : ℕ →₀ ℕ} (h : ∀ t, ¬ AccelZeckMove s t) :
    AccelZeckLosing s :=
  .intro s fun t ht => absurd ht (h t)

/-- **The first player wins the game on $2$.** The state consisting of two copies of $F_1$ is
winning.

The winning move is $1 \cdot C_1$, which reaches the terminal state with one copy of $F_2$.

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

/-- **Zeckendorf decomposition as a game state.** Index the Fibonacci numbers as $F_1 = 1$,
$F_2 = 2$ and $F_{i+1} = F_i + F_{i-1}$, and record a game state as a finitely supported
function $s : \mathbb{N} \to \mathbb{N}$, where $s(i)$ is the number of copies of $F_i$. Every
$n \in \mathbb{N}$ has a unique Zeckendorf decomposition $n = F_{i_1} + \cdots + F_{i_r}$ with
$r \ge 0$, indices $i_1, \dots, i_r \ge 1$ and $i_t \ge i_{t+1} + 2$ for $1 \le t < r$. The
Zeckendorf state of $n$ is the game state with one copy of each $F_{i_t}$: $s(i) = 1$ if
$i \in \{i_1, \dots, i_r\}$ and $s(i) = 0$ otherwise.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 1.1 and Theorem 1.3. -/
public def zeckendorfState (n : ℕ) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (((Nat.zeckendorf n).map (· - 1) : List ℕ) : Multiset ℕ)

/-- **The Zeckendorf state of zero is empty.** The Zeckendorf state of $0$ is the empty game
state, with no copies of any Fibonacci number.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Section 1.1. -/
public theorem zeckendorfState_zero : zeckendorfState 0 = 0 := by
  simp [zeckendorfState]

/-- **The Zeckendorf state of $4$.** The Zeckendorf state of $4$ consists of one copy of $F_3$
and one copy of $F_1$, reflecting the Zeckendorf decomposition $4 = F_3 + F_1 = 3 + 1$.

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

-- The extra weight at index 2 makes even the split 2 + 2 → 1 + 3 decrease the rank.
private def accelZeckWeight (i : ℕ) : ℕ :=
  2 * i + 2 + if i = 2 then 1 else 0

private def accelZeckRank : (ℕ →₀ ℕ) →+ ℕ where
  toFun s := s.sum fun i m => m * accelZeckWeight i
  map_zero' := by simp
  map_add' s t := Finsupp.sum_add_index' (fun _ => Nat.zero_mul _) (fun _ _ _ => Nat.add_mul ..)

private theorem accelZeckRank_single (i m : ℕ) :
    accelZeckRank (Finsupp.single i m) = m * accelZeckWeight i :=
  Finsupp.sum_single_index (h := fun i m => m * accelZeckWeight i) (Nat.zero_mul _)

private theorem accelZeckRank_remove {s : ℕ →₀ ℕ} {i m : ℕ} (h : m ≤ s i) :
    accelZeckRank (s - Finsupp.single i m) + m * accelZeckWeight i = accelZeckRank s := by
  rw [← accelZeckRank_single, ← map_add, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h)]

private theorem accelZeckRank_lt {s t : ℕ →₀ ℕ} (h : AccelZeckMove s t) :
    accelZeckRank t < accelZeckRank s := by
  rcases h with ⟨m, hm, ⟨i, hi, h₁, h₂, rfl⟩ | ⟨h₁, rfl⟩ | ⟨h₂, rfl⟩ | ⟨i, hi, hᵢ, rfl⟩⟩
  · have hcost : accelZeckWeight (i + 1) < accelZeckWeight (i - 1) + accelZeckWeight i := by
      unfold accelZeckWeight
      split_ifs <;> omega
    have h₂' : m ≤ (s - Finsupp.single (i - 1) m) i := by
      simpa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (show i ≠ i - 1 by omega)] using h₂
    have hremove₁ := accelZeckRank_remove h₁
    have hremove₂ := accelZeckRank_remove h₂'
    have hlt := Nat.mul_lt_mul_of_pos_left hcost hm
    rw [Nat.mul_add] at hlt
    rw [map_add, accelZeckRank_single]
    omega
  · have hremove := accelZeckRank_remove h₁
    rw [map_add, accelZeckRank_single]
    simp [accelZeckWeight, Nat.mul_comm m] at hremove ⊢
    omega
  · have hremove := accelZeckRank_remove h₂
    simp only [map_add, accelZeckRank_single] at ⊢
    simp [accelZeckWeight, Nat.mul_comm m] at hremove ⊢
    omega
  · have hcost : accelZeckWeight (i - 2) + accelZeckWeight (i + 1) <
        2 * accelZeckWeight i := by
      unfold accelZeckWeight
      split_ifs <;> omega
    have hremove := accelZeckRank_remove hᵢ
    have hlt := Nat.mul_lt_mul_of_pos_left hcost hm
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm m 2] at hlt
    simp only [map_add, accelZeckRank_single]
    omega

private theorem accelZeckLosing_iff_not_winning (s : ℕ →₀ ℕ) :
    AccelZeckLosing s ↔ ¬ AccelZeckWinning s := by
  refine (measure fun s => accelZeckRank s).wf.induction
    (C := fun s => AccelZeckLosing s ↔ ¬ AccelZeckWinning s) s ?_
  intro s ih
  constructor
  · intro hl hw
    obtain ⟨t, hmove, htl⟩ := (accelZeckWinning_iff s).mp hw
    cases hl with
    | intro _ hnext => exact (ih t (accelZeckRank_lt hmove)).mp htl (hnext t hmove)
  · intro hn
    refine .intro s fun t hmove => ?_
    by_contra ht
    exact hn (.intro s t hmove ((ih t (accelZeckRank_lt hmove)).mpr ht))

private noncomputable def accelZeckPiles (a b c : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 1 a + Finsupp.single 2 b + Finsupp.single 3 c

/-- **Accelerated Zeckendorf Game: Conjecture 1.7 implies Conjecture 1.6.** Index the Fibonacci
numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Suppose that for every $n$ such that
the state consisting of $n$ copies of $F_1$ is losing, and every $k$ with $3k \le n$, the state
consisting of $k$ copies of $F_3$ and $n - 3k$ copies of $F_1$ is losing. Then for every $n > 9$
the state consisting of $n$ copies of $F_1$ (the starting position of the Accelerated Zeckendorf
Game on $n$) is winning.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.8 (with Conjectures 1.6 and 1.7). -/
public theorem accelZeck_conjecture17_implies_conjecture16
    (h17 : ∀ n, AccelZeckLosing (Finsupp.single 1 n) → ∀ k, 3 * k ≤ n →
      AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k))) :
    ∀ n, 9 < n → AccelZeckWinning (Finsupp.single 1 n) := by
  intro n hn
  by_contra h
  have hlose := (accelZeckLosing_iff_not_winning _).mpr h
  -- Take the largest odd integer at most n / 2. It is strictly larger than n / 3.
  obtain ⟨k, hk, h₂k, h₃k⟩ : ∃ k : ℕ, k % 2 = 1 ∧ 2 * k ≤ n ∧ n < 3 * k := by
    exact ⟨2 * ((n - 2) / 4) + 1, by omega, by omega, by omega⟩
  let s := accelZeckPiles (n - 2 * k) k 0
  have hfirst : AccelZeckMove (Finsupp.single 1 n) s := by
    refine ⟨k, by omega, Or.inr (Or.inl ⟨by simpa, ?_⟩)⟩
    simp [s, accelZeckPiles, ← Finsupp.single_tsub]
  have hs : AccelZeckWinning s := by
    cases hlose with
    | intro _ hnext => exact hnext s hfirst
  obtain ⟨t, hmove, ht⟩ := (accelZeckWinning_iff s).mp hs
  apply (accelZeckLosing_iff_not_winning t).mp ht
  -- Every reply leaves a positive number of twos, so it can also be reached by
  -- combining ones from a state assumed losing by Conjecture 1.7.
  have hreply (a b : ℕ) (hb : 0 < b) (hab : 3 * a + 2 * b ≤ n) :
      AccelZeckWinning (accelZeckPiles (n - 3 * a - 2 * b) b a) := by
    have hl := h17 n hlose a (by omega)
    have hm : AccelZeckMove (Finsupp.single 3 a + Finsupp.single 1 (n - 3 * a))
        (accelZeckPiles (n - 3 * a - 2 * b) b a) := by
      refine ⟨b, hb, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide : 1 ≠ 3),
          Finsupp.single_eq_same, zero_add]
        omega
      · ext i
        simp only [accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs <;> omega
    cases hl with
    | intro _ hnext => exact hnext _ hm
  rcases hmove with ⟨m, hm, ⟨i, hi, h₁, h₂, rfl⟩ | ⟨h₁, rfl⟩ | ⟨h₂, rfl⟩ | ⟨i, hi, hᵢ, rfl⟩⟩
  · have hi₂ : i = 2 := by
      by_contra hne
      have hz : s i = 0 := by
        simp [s, accelZeckPiles, Finsupp.single_eq_of_ne (show i ≠ 1 by omega),
          Finsupp.single_eq_of_ne hne]
      omega
    subst i
    have h₁' : m ≤ n - 2 * k := by simpa [s, accelZeckPiles] using h₁
    have h₂' : m ≤ k := by simpa [s, accelZeckPiles] using h₂
    have heq : s - Finsupp.single 1 m - Finsupp.single 2 m + Finsupp.single 3 m =
        accelZeckPiles (n - 3 * m - 2 * (k - m)) (k - m) m := by
      ext i
      simp only [s, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    change AccelZeckWinning (s - Finsupp.single 1 m - Finsupp.single 2 m + Finsupp.single 3 m)
    rw [heq]
    exact hreply m (k - m) (by omega) (by omega)
  · have h₁' : 2 * m ≤ n - 2 * k := by simpa [s, accelZeckPiles] using h₁
    have heq : s - Finsupp.single 1 (2 * m) + Finsupp.single 2 m =
        accelZeckPiles (n - 3 * 0 - 2 * (k + m)) (k + m) 0 := by
      ext i
      simp only [s, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [heq]
    exact hreply 0 (k + m) (by omega) (by omega)
  · have h₂' : 2 * m ≤ k := by simpa [s, accelZeckPiles] using h₂
    have heq : s - Finsupp.single 2 (2 * m) + Finsupp.single 1 m + Finsupp.single 3 m =
        accelZeckPiles (n - 3 * m - 2 * (k - 2 * m)) (k - 2 * m) m := by
      ext i
      simp only [s, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [heq]
    exact hreply m (k - 2 * m) (by omega) (by omega)
  · have hz : s i = 0 := by
      simp [s, accelZeckPiles, Finsupp.single_eq_of_ne (show i ≠ 1 by omega),
        Finsupp.single_eq_of_ne (show i ≠ 2 by omega)]
    omega

/-- **Unique losing move from $k$ copies of $F_2$ for odd $k$.** Let $k$ be odd and $n \ge 2k$,
and suppose that for every $i < k$ with $3i \le n$ the state with $i$ copies of $F_3$,
$n - 3i$ copies of $F_1$ and nothing else is losing. Then $n \ge 3k$; the state $T$ with $k$
copies of $F_3$, $n - 3k$ copies of $F_1$ and nothing else is losing and is reached in one
move from the state $S$ with $k$ copies of $F_2$, $n - 2k$ copies of $F_1$ and nothing else;
and every losing state reached in one move from $S$ equals $T$.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.4. -/
public theorem accelZeck_odd_unique_losing_move (k n : ℕ) (hk : Odd k) (hn : 2 * k ≤ n)
    (hlose : ∀ i < k, 3 * i ≤ n →
      AccelZeckLosing (Finsupp.single 3 i + Finsupp.single 1 (n - 3 * i))) :
    3 * k ≤ n ∧
      AccelZeckMove (Finsupp.single 2 k + Finsupp.single 1 (n - 2 * k))
        (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k)) ∧
      AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k)) ∧
      ∀ t, AccelZeckMove (Finsupp.single 2 k + Finsupp.single 1 (n - 2 * k)) t →
        AccelZeckLosing t → t = Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k) := by
  let s := accelZeckPiles (n - 2 * k) k 0
  let u := accelZeckPiles (n - 3 * k) 0 k
  suffices h : 3 * k ≤ n ∧ AccelZeckMove s u ∧ AccelZeckLosing u ∧
      ∀ t, AccelZeckMove s t → AccelZeckLosing t → t = u by
    simpa [s, u, accelZeckPiles, add_comm] using h
  obtain ⟨r, hr⟩ := hk
  -- Every such state with positive twos comes from an assumed losing state by a C₁ move.
  have hwinning (a b : ℕ) (ha : a < k) (hb : 0 < b) (hab : 3 * a + 2 * b ≤ n) :
      AccelZeckWinning (accelZeckPiles (n - 3 * a - 2 * b) b a) := by
    obtain ⟨_, hnext⟩ := hlose a ha (by omega)
    apply hnext
    refine ⟨b, hb, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · simp
      omega
    · ext i
      simp only [accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
  have hnotLosing (a b : ℕ) (ha : a < k) (hb : 0 < b) (hab : 3 * a + 2 * b ≤ n) :
      ¬ AccelZeckLosing (accelZeckPiles (n - 3 * a - 2 * b) b a) :=
    fun hl => (accelZeckLosing_iff_not_winning _).mp hl (hwinning a b ha hb hab)
  have hs_zero {i : ℕ} (hi : 2 < i) : s i = 0 := by
    simp [s, accelZeckPiles, Finsupp.single_eq_of_ne (show i ≠ 1 by omega),
      Finsupp.single_eq_of_ne (show i ≠ 2 by omega)]
  have hs : AccelZeckWinning s := by
    simpa [s] using hwinning 0 k (by omega) (by omega) (by omega)
  have hforced {t : ℕ →₀ ℕ} (hmove : AccelZeckMove s t) (ht : AccelZeckLosing t) :
      3 * k ≤ n ∧ t = u := by
    -- Only combining all k twos with ones can avoid leaving a winning state.
    rcases hmove with ⟨m, hm, ⟨i, hi, h₁, h₂, rfl⟩ | ⟨h₁, rfl⟩ | ⟨h₂, rfl⟩ | ⟨i, hi, hᵢ, -⟩⟩
    · have hi₂ : i = 2 := by
        by_contra hne
        have hz := hs_zero (show 2 < i by omega)
        omega
      subst i
      have h₁' : m ≤ n - 2 * k := by simpa [s, accelZeckPiles] using h₁
      have h₂' : m ≤ k := by simpa [s, accelZeckPiles] using h₂
      by_cases hmk : m = k
      · subst m
        refine ⟨by omega, ?_⟩
        ext j
        simp only [s, u, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply,
          Finsupp.single_apply]
        split_ifs <;> omega
      · have hdest : s - Finsupp.single 1 m - Finsupp.single 2 m + Finsupp.single 3 m =
            accelZeckPiles (n - 3 * m - 2 * (k - m)) (k - m) m := by
          ext j
          simp only [s, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs <;> omega
        exact (hnotLosing m (k - m) (by omega) (by omega) (by omega) (hdest ▸ ht)).elim
    · have h₁' : 2 * m ≤ n - 2 * k := by simpa [s, accelZeckPiles] using h₁
      have hdest : s - Finsupp.single 1 (2 * m) + Finsupp.single 2 m =
          accelZeckPiles (n - 3 * 0 - 2 * (k + m)) (k + m) 0 := by
        ext j
        simp only [s, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs <;> omega
      exact (hnotLosing 0 (k + m) (by omega) (by omega) (by omega) (hdest ▸ ht)).elim
    · have h₂' : 2 * m ≤ k := by simpa [s, accelZeckPiles] using h₂
      have hdest : s - Finsupp.single 2 (2 * m) + Finsupp.single 1 m + Finsupp.single 3 m =
          accelZeckPiles (n - 3 * m - 2 * (k - 2 * m)) (k - 2 * m) m := by
        ext j
        simp only [s, accelZeckPiles, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs <;> omega
      -- Oddness makes the number of remaining twos strictly positive after a split.
      exact (hnotLosing m (k - 2 * m) (by omega) (by omega) (by omega) (hdest ▸ ht)).elim
    · have hz := hs_zero (show 2 < i by omega)
      omega
  obtain ⟨t, hmove, ht⟩ := (accelZeckWinning_iff s).mp hs
  obtain ⟨hbound, rfl⟩ := hforced hmove ht
  exact ⟨hbound, hmove, ht, fun _ hmove' ht' => (hforced hmove' ht').2⟩

private theorem accelZeckMove_from_ones {n : ℕ} {t : ℕ →₀ ℕ}
    (h : AccelZeckMove (Finsupp.single 1 n) t) :
    ∃ m, 0 < m ∧ 2 * m ≤ n ∧ t = Finsupp.single 1 (n - 2 * m) + Finsupp.single 2 m := by
  rcases h with ⟨m, hm, ⟨i, hi, -, hs, -⟩ | ⟨hs, rfl⟩ | ⟨hs, -⟩ | ⟨i, hi, hs, -⟩⟩
  · simp [Finsupp.single_eq_of_ne (show i ≠ 1 by omega)] at hs
    omega
  · exact ⟨m, hm, by simpa using hs, by rw [Finsupp.single_tsub]⟩
  · simp at hs
    omega
  · simp [Finsupp.single_eq_of_ne (show i ≠ 1 by omega)] at hs
    omega

-- Combining the additional pairs of ones reaches the larger opening position.
private theorem accelZeckMove_between_openings {n a b : ℕ} (hab : a < b) (hb : 2 * b ≤ n) :
    AccelZeckMove (Finsupp.single 1 (n - 2 * a) + Finsupp.single 2 a)
      (Finsupp.single 1 (n - 2 * b) + Finsupp.single 2 b) := by
  refine ⟨b - a, by omega, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
  · simp
    omega
  · ext i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> omega

/-- **Unique winning first move.** For every $n$, if the state consisting of $n$ copies of $F_1$
is winning, then exactly one state reachable from it in one move is losing: when the first
player has a winning strategy in the game on $n$, exactly one first move preserves it.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Proposition 1.5. -/
public theorem accelZeck_unique_winning_first_move (n : ℕ)
    (h : AccelZeckWinning (Finsupp.single 1 n)) :
    ∃! t, AccelZeckMove (Finsupp.single 1 n) t ∧ AccelZeckLosing t := by
  obtain ⟨t, ht, htl⟩ := (accelZeckWinning_iff _).mp h
  refine ⟨t, ⟨ht, htl⟩, ?_⟩
  rintro u ⟨hu, hul⟩
  obtain ⟨a, _, ha, rfl⟩ := accelZeckMove_from_ones ht
  obtain ⟨b, _, hb, rfl⟩ := accelZeckMove_from_ones hu
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact ((accelZeckLosing_iff_not_winning _).mp htl
      (.intro _ _ (accelZeckMove_between_openings hab hb) hul)).elim
  · rfl
  · exact ((accelZeckLosing_iff_not_winning _).mp hul
      (.intro _ _ (accelZeckMove_between_openings hba ha) htl)).elim

end

end MetaMathlibExt
