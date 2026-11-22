/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.ListRanking
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Suffix sums on linked lists by pointer jumping

Wyllie's pointer jumping (Wyllie, *The Complexity of Parallel Computations*, PhD thesis, Cornell,
1979; JáJá, *An Introduction to Parallel Algorithms*, Chapter 3) computes, for nodes `Fin n`
linked through `succ` and values `x` in any additive monoid (not necessarily commutative), every
node's suffix sum: the values from the node to the end of its list, in list order. List ranking
(`ListRanking.lean`) is the special case of unit values (`suffixSum_one`).

Main results:

* `segSum` (the sum over the first `k` nodes from `v`), `segSum_add`; `suffixSum` with its
  characteristic property `suffixSum_eq` (a node's value plus its successor's suffix sum).
* `rounds_spec` (**the invariant**): after `t` rounds each pointer is `2 ^ t` steps ahead and each
  sum covers the first `2 ^ t` nodes; `rounds_acc`: with `n ≤ 2 ^ t`, the sums are the suffix
  sums.
* `listSums_getD`: **pointer jumping computes all suffix sums in `⌈log₂ n⌉` rounds**; `listSums`
  runs the rounds on arrays (`roundsTab`, `roundsTab_eq`).
* `segSum_one`, `suffixSum_one`: with unit values in `ℕ` the suffix sums are the ranks plus one.

## Cost model

As for list ranking: a round is one parallel step in which every node reads its target's pointer
and sum (CREW PRAM style), and `listSums` runs `Nat.clog 2 n` rounds. Simulated sequentially on
arrays each round is `n` reads, writes and additions, `O(n log n)` in total; the parallel work is
not optimal (work-optimal list ranking needs further ideas, not formalized).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Parallel.ListPrefix

open Cslib.Algorithms.Lean.Parallel.ListRanking

variable {n : ℕ} {M : Type*} [AddMonoid M]

/-- The value of the node `k` steps after `v`, or `0` past the end. -/
def stepVal (succ : Fin n → Option (Fin n)) (x : Fin n → M) (k : ℕ) (v : Fin n) : M :=
  match jump succ k v with
  | some u => x u
  | none => 0

/-- The sum of the values of the first `k` nodes from `v` on (fewer at the end of the list), in
list order. -/
def segSum (succ : Fin n → Option (Fin n)) (x : Fin n → M) : ℕ → Fin n → M
  | 0, _ => 0
  | k + 1, v => segSum succ x k v + stepVal succ x k v

variable {succ : Fin n → Option (Fin n)} {x : Fin n → M}

/-- Segments add up: the first `a + b` nodes are the first `a`, then `b` from where those end. -/
theorem segSum_add (a b : ℕ) (v : Fin n) : segSum succ x (a + b) v =
    segSum succ x a v + match jump succ a v with
      | some u => segSum succ x b u
      | none => 0 := by
  induction b with
  | zero => cases jump succ a v <;> simp [segSum]
  | succ b ih =>
      rw [← Nat.add_assoc, segSum, ih]
      have hj := jump_add (succ := succ) a b v
      simp only [stepVal, hj]
      cases jump succ a v with
      | none => simp
      | some u => simp [segSum, stepVal, add_assoc]

/-- The suffix sum of `v`: the values from `v` to the end of its list, in list order. -/
def suffixSum (succ : Fin n → Option (Fin n)) (x : Fin n → M) (v : Fin n) : M := segSum succ x n v

theorem segSum_of_le (hs : Terminates succ) {k : ℕ} (hk : n ≤ k) (v : Fin n) :
    segSum succ x k v = suffixSum succ x v := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [segSum_add, hs v, suffixSum]
  simp

/-- **The characteristic property of suffix sums**: a node's suffix sum is its value plus its
successor's suffix sum. -/
theorem suffixSum_eq (hs : Terminates succ) (v : Fin n) :
    suffixSum succ x v = x v + match succ v with
      | some u => suffixSum succ x u
      | none => 0 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => (h ▸ v).elim0
  have key := segSum_add (succ := succ) (x := x) 1 (n - 1) v
  rw [show 1 + (n - 1) = n by omega] at key
  have h1 : segSum succ x 1 v = x v := by simp [segSum, stepVal, jump]
  have hj1 : jump succ 1 v = succ v := by simp [jump]
  rw [suffixSum, key, h1, hj1]
  cases hsv : succ v with
  | none => rfl
  | some u =>
      simp only
      -- `n - 1` steps from `u` already run off the end
      have hr := rank_of_jump hs (show jump succ 1 v = some u by rw [hj1, hsv])
      have hrv := rank_lt hs v
      have hju : jump succ (n - 1) u = none := (jump_eq_none_iff hs u _).2 (by omega)
      have k2 : segSum succ x (n - 1 + 1) u = segSum succ x (n - 1) u := by
        rw [segSum, stepVal, hju, add_zero]
      rw [show n - 1 + 1 = n by omega] at k2
      rw [suffixSum, k2]

/-- **List ranking is the special case of unit values**: summing `1` over the first `k` nodes
from `v` counts `min k (rank v + 1)` nodes. -/
theorem segSum_one (hs : Terminates succ) (k : ℕ) (v : Fin n) :
    segSum succ (fun _ => (1 : ℕ)) k v = min k (rank hs v + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [segSum, ih, stepVal]
      cases hj : jump succ k v with
      | none =>
          have := (jump_eq_none_iff hs v k).1 hj
          simp only [Nat.add_zero]
          omega
      | some u =>
          have : ¬ rank hs v < k := fun h => by
            rw [(jump_eq_none_iff hs v k).2 h] at hj; cases hj
          simp only
          omega

/-- Suffix sums of unit values are the ranks plus one. -/
theorem suffixSum_one (hs : Terminates succ) (v : Fin n) :
    suffixSum succ (fun _ => (1 : ℕ)) v = rank hs v + 1 := by
  rw [suffixSum, segSum_one hs]
  have := rank_lt hs v
  omega

/-! ## Pointer jumping -/

/-- The state of pointer jumping: each node's pointer and the sum of the values it has covered. -/
structure State (n : ℕ) (M : Type*) where
  /-- The node's pointer (`none` once it points past the end). -/
  ptr : Fin n → Option (Fin n)
  /-- The sum of the values from the node up to, not including, the pointer's target. -/
  acc : Fin n → M

/-- The initial state: pointers are the successors, sums the nodes' own values. -/
def init (succ : Fin n → Option (Fin n)) (x : Fin n → M) : State n M := ⟨succ, x⟩

/-- One parallel round: every node adds its target's sum to its own (on the right, keeping list
order) and jumps to its target's target. -/
def round (s : State n M) : State n M :=
  ⟨fun v => (s.ptr v).bind s.ptr, fun v =>
    match s.ptr v with
    | none => s.acc v
    | some u => s.acc v + s.acc u⟩

/-- The state after `t` rounds. -/
def rounds (succ : Fin n → Option (Fin n)) (x : Fin n → M) : ℕ → State n M
  | 0 => init succ x
  | t + 1 => round (rounds succ x t)

/-- **The invariant of pointer jumping**: after `t` rounds each pointer is `2 ^ t` steps ahead
and each sum covers the first `2 ^ t` nodes. -/
theorem rounds_spec : ∀ t v, (rounds succ x t).ptr v = jump succ (2 ^ t) v ∧
    (rounds succ x t).acc v = segSum succ x (2 ^ t) v
  | 0, v => ⟨by simp [rounds, init, jump], by simp [rounds, init, segSum, stepVal, jump]⟩
  | t + 1, v => by
      obtain ⟨hp, ha⟩ := rounds_spec t v
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega
      refine ⟨?_, ?_⟩
      · simp only [rounds, round, hp, hpow, jump_add]
        congr 1
        funext u
        exact (rounds_spec t u).1
      · simp only [rounds, round, hp, hpow, segSum_add]
        cases jump succ (2 ^ t) v with
        | none => simp [ha]
        | some u => simp [ha, (rounds_spec t u).2]

/-- After `t` rounds with `n ≤ 2 ^ t`, every sum is the suffix sum. -/
theorem rounds_acc (hs : Terminates succ) {t : ℕ} (ht : n ≤ 2 ^ t) (v : Fin n) :
    (rounds succ x t).acc v = suffixSum succ x v := by
  rw [(rounds_spec t v).2, segSum_of_le hs ht]

/-! ## Tabulated rounds -/

/-- A state stored in arrays: evaluating `rounds` directly re-reads earlier rounds at every query,
a cost exponential in the number of rounds; on arrays each round costs `O(n)` operations. -/
def tabulate (s : State n M) : Array (Option (Fin n)) × Array M :=
  (Array.ofFn s.ptr, Array.ofFn s.acc)

/-- One round on arrays. -/
def roundTab (s : Array (Option (Fin n)) × Array M) : Array (Option (Fin n)) × Array M :=
  (Array.ofFn fun v : Fin n => (s.1.getD v none).bind fun u => s.1.getD u none,
    Array.ofFn fun v : Fin n =>
      match s.1.getD v none with
      | none => s.2.getD v 0
      | some u => s.2.getD v 0 + s.2.getD u 0)

/-- The arrays after `t` rounds. -/
def roundsTab (succ : Fin n → Option (Fin n)) (x : Fin n → M) :
    ℕ → Array (Option (Fin n)) × Array M
  | 0 => tabulate (init succ x)
  | t + 1 => roundTab (roundsTab succ x t)

private theorem getD_ofFn {α : Type*} (f : Fin n → α) (v : Fin n) (d : α) :
    (Array.ofFn f).getD v d = f v := by
  simp [v.isLt]

theorem roundTab_tabulate (s : State n M) : roundTab (tabulate s) = tabulate (round s) := by
  simp only [roundTab, tabulate, round, getD_ofFn]

theorem roundsTab_eq (succ : Fin n → Option (Fin n)) (x : Fin n → M) :
    ∀ t, roundsTab succ x t = tabulate (rounds succ x t)
  | 0 => rfl
  | t + 1 => by rw [roundsTab, roundsTab_eq succ x t, roundTab_tabulate]; rfl

/-- Suffix sums by pointer jumping: `⌈log₂ n⌉` rounds (`Nat.clog 2 n`) on arrays, returning the
whole table (entry `v` is the suffix sum of node `v`). -/
def listSums (succ : Fin n → Option (Fin n)) (x : Fin n → M) : Array M :=
  (roundsTab succ x (Nat.clog 2 n)).2

theorem size_listSums (succ : Fin n → Option (Fin n)) (x : Fin n → M) :
    (listSums succ x).size = n := by
  rw [listSums, roundsTab_eq, tabulate, Array.size_ofFn]

/-- **Pointer jumping computes all suffix sums in `⌈log₂ n⌉` rounds.** -/
theorem listSums_getD (hs : Terminates succ) (v : Fin n) :
    (listSums succ x).getD v 0 = suffixSum succ x v := by
  rw [listSums, roundsTab_eq, tabulate, getD_ofFn]
  exact rounds_acc hs (Nat.le_pow_clog (by decide) n) v

end Cslib.Algorithms.Lean.Parallel.ListPrefix
