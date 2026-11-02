/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Nat.Log

/-!
# List ranking by pointer jumping

List ranking (Wyllie, *The Complexity of Parallel Computations*, PhD thesis, Cornell, 1979; CLRS,
first edition, Section 30.1.1): nodes `Fin n` form linked lists through `succ`, and each node's
rank is the number of nodes after it. Pointer jumping runs `⌈log₂ n⌉` parallel rounds; in each,
every node adds its target's distance to its own and jumps to its target's target.

Main results:

* `jump`, `jump_add`; `rank` with its characteristic property `jump_eq_none_iff` (`k` steps run
  off the end exactly when `k > rank v`), `rank_of_jump`, `rank_lt`.
* `rounds_spec` (**the invariant**): after `t` rounds each pointer is `2 ^ t` steps ahead and the
  distance is `min (2 ^ t) (rank v)`; `rounds_dist`: after `t` rounds with `n ≤ 2 ^ t` the
  distances are the ranks.
* `listRanks_getD`: **pointer jumping ranks every list in `⌈log₂ n⌉` rounds**; `listRanks` runs the
  rounds on arrays (`roundsTab`, `roundsTab_eq`).

## Cost model

A round is one parallel step in which every node reads its target's pointer and distance (CREW
PRAM style); `listRanks` runs `Nat.clog 2 n` rounds and returns all ranks at once. Simulated
sequentially on arrays, each round is `n` reads and writes, `O(n log n)` in total.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Parallel.ListRanking

variable {n : ℕ}

/-- **Iterated successor.** For a successor map $\mathrm{succ}$ on the nodes $0, \dots, n-1$, where
$\mathrm{succ}(v)$ is either a node or undefined, the $k$-step jump from $v$ is the node reached by
applying $\mathrm{succ}$ $k$ times starting at $v$, and is undefined if some step is undefined: the
$0$-step jump from $v$ is $v$, and the $(k+1)$-step jump is $\mathrm{succ}$ of the $k$-step jump. -/
def jump (succ : Fin n → Option (Fin n)) : ℕ → Fin n → Option (Fin n)
  | 0, v => some v
  | k + 1, v => (jump succ k v).bind succ

/-- **Terminating successor functions.** A successor function $\mathrm{succ}$ on the nodes
$0, \dots, n - 1$, mapping each node to its successor or to nothing, terminates when from every
node $v$ the walk of $n$ steps along $\mathrm{succ}$ runs off the end, that is, there is no node
$n$ steps down the list from $v$. -/
def Terminates (succ : Fin n → Option (Fin n)) : Prop := ∀ v, jump succ n v = none

variable {succ : Fin n → Option (Fin n)}

theorem jump_add (a b : ℕ) (v : Fin n) :
    jump succ (a + b) v = (jump succ a v).bind (jump succ b) := by
  induction b with
  | zero => cases jump succ a v <;> rfl
  | succ b ih =>
      change (jump succ (a + b) v).bind succ = _
      rw [ih]
      cases jump succ a v <;> rfl

theorem jump_eq_none_mono {a b : ℕ} (hab : a ≤ b) {v : Fin n} (h : jump succ a v = none) :
    jump succ b v = none := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [jump_add, h]
  rfl

/-- **Rank of a node in a linked list.** Let $\mathrm{succ}$ be a successor map on the nodes
$0, \dots, n-1$ whose lists terminate. The rank of a node $v$ is the least $k$ such that following
$\mathrm{succ}$ for $k + 1$ steps from $v$ runs off the end of the list, that is, the number of
nodes after $v$ in its list. -/
noncomputable def rank (hs : Terminates succ) (v : Fin n) : ℕ :=
  Nat.find (p := fun k => jump succ (k + 1) v = none) ⟨n - 1, by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact v.elim0
    · rw [Nat.sub_add_cancel hn]; exact hs v⟩

/-- **The characteristic property of the rank.** Let $\mathrm{succ}$ be a successor map on the
nodes $0, \dots, n-1$ whose lists terminate. For every node $v$ and every $k \in \mathbb{N}$,
following $\mathrm{succ}$ for $k$ steps from $v$ runs off the end of the list if and only if
$k > \operatorname{rank}(v)$. -/
theorem jump_eq_none_iff (hs : Terminates succ) (v : Fin n) (k : ℕ) :
    jump succ k v = none ↔ rank hs v < k := by
  constructor
  · intro h
    rcases k with _ | k
    · simp [jump] at h
    · exact Nat.lt_succ_of_le (Nat.find_min' _ h)
  · intro h
    exact jump_eq_none_mono h (Nat.find_spec (p := fun k => jump succ (k + 1) v = none) _)

/-- Two thresholds characterizing the same property are equal. -/
private theorem eq_of_lt_iff {r r' : ℕ} (h : ∀ k, r < k ↔ r' < k) : r = r' := by
  have h1 := (h (r + 1)).1 (Nat.lt_succ_self r)
  have h2 := (h (r' + 1)).2 (Nat.lt_succ_self r')
  omega

/-- **Rank decreases along jumps.** Let $\mathrm{succ}$ be a successor map on the nodes
$0, \dots, n-1$ whose lists terminate. If following $\mathrm{succ}$ for $a$ steps from a node $v$
reaches the node $u$, then $a \le \operatorname{rank}(v)$ and
$\operatorname{rank}(u) = \operatorname{rank}(v) - a$. -/
theorem rank_of_jump (hs : Terminates succ) {a : ℕ} {v u : Fin n} (h : jump succ a v = some u) :
    a ≤ rank hs v ∧ rank hs u = rank hs v - a := by
  have ha : a ≤ rank hs v := by
    by_contra hlt
    have := (jump_eq_none_iff hs v a).2 (by omega)
    rw [h] at this
    exact Option.some_ne_none _ this
  refine ⟨ha, eq_of_lt_iff fun k => ?_⟩
  rw [← jump_eq_none_iff hs u k, show jump succ k u = jump succ (a + k) v by rw [jump_add, h]; rfl,
    jump_eq_none_iff hs v]
  omega

theorem rank_lt (hs : Terminates succ) (v : Fin n) : rank hs v < n :=
  (jump_eq_none_iff hs v n).1 (hs v)

/-! ## Pointer jumping -/

/-- **Pointer-jumping state for list ranking.** A pointer-jumping state on the nodes
$0, \dots, n - 1$ assigns to each node a pointer, which is either a node or empty (once it points
past the end of the list), and a distance in $\mathbb{N}$, the distance covered by the pointer. -/
structure State (n : ℕ) where
  /-- The node's pointer (`none` once it points past the end). -/
  ptr : Fin n → Option (Fin n)
  /-- The distance covered by the pointer. -/
  dist : Fin n → ℕ

/-- **Initial state of pointer jumping.** For a successor map $\mathrm{succ}$ on the nodes
$0, \dots, n-1$, where $\mathrm{succ}(v)$ is either a node or undefined (at the end of a list), the
initial pointer-jumping state gives each node $v$ the pointer $\mathrm{succ}(v)$ and the distance
$0$ if $\mathrm{succ}(v)$ is undefined and $1$ otherwise. -/
def init (succ : Fin n → Option (Fin n)) : State n :=
  ⟨succ, fun v => if succ v = none then 0 else 1⟩

/-- **One round of pointer jumping.** In one parallel round, every node $v$ whose pointer is a node
$u$ adds the distance of $u$ to its own distance and moves its pointer to the pointer of $u$
(undefined if that of $u$ is); a node whose pointer is undefined keeps its distance and its
undefined pointer. -/
def round (s : State n) : State n :=
  ⟨fun v => (s.ptr v).bind s.ptr, fun v =>
    match s.ptr v with
    | none => s.dist v
    | some u => s.dist v + s.dist u⟩

/-- **The list-ranking state after $t$ rounds.** For a successor function $\mathrm{succ}$ on the
nodes $0, \dots, n - 1$, the pointer-jumping state after $t$ rounds is defined by recursion on
$t$: after $0$ rounds it is the initial state of $\mathrm{succ}$, and after $t + 1$ rounds it is
one round of pointer jumping applied to the state after $t$ rounds. -/
def rounds (succ : Fin n → Option (Fin n)) : ℕ → State n
  | 0 => init succ
  | t + 1 => round (rounds succ t)

/-- **The invariant of pointer jumping for list ranking.** Let $\mathrm{succ}$ map each of the
nodes $0, \dots, n - 1$ to its successor or to nothing, and suppose the lists terminate: from
every node, $n$ steps run off the end. Write $\mathrm{rank}(v)$ for the number of nodes after
$v$. Then for every $t \ge 0$ and every node $v$, after $t$ rounds of pointer jumping, the
pointer of $v$ is the node $2^t$ steps down the list from $v$ (no node if the list ends before
that), and the distance of $v$ is $\min(2^t, \mathrm{rank}(v))$. -/
theorem rounds_spec (hs : Terminates succ) : ∀ t v,
    (rounds succ t).ptr v = jump succ (2 ^ t) v ∧
      (rounds succ t).dist v = min (2 ^ t) (rank hs v)
  | 0, v => by
      refine ⟨by simp [rounds, init, jump], ?_⟩
      have h : succ v = none ↔ rank hs v < 1 := jump_eq_none_iff hs v 1
      simp only [rounds, init, Nat.pow_zero]
      split_ifs with h0
      · have := h.1 h0; omega
      · have : ¬ rank hs v < 1 := fun hr => h0 (h.2 hr)
        omega
  | t + 1, v => by
      obtain ⟨hp, hd⟩ := rounds_spec hs t v
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega
      refine ⟨?_, ?_⟩
      · simp only [rounds, round, hp, hpow, jump_add]
        congr 1
        funext u
        exact (rounds_spec hs t u).1
      · simp only [rounds, round, hp]
        cases hj : jump succ (2 ^ t) v with
        | none =>
            have := (jump_eq_none_iff hs v _).1 hj
            simp only [hd]
            omega
        | some u =>
            obtain ⟨hle, hu⟩ := rank_of_jump hs hj
            simp only [hd, (rounds_spec hs t u).2, hu]
            omega

/-- **After enough rounds, the distances are the ranks.** Let $\mathrm{succ}$ be a successor map
on the nodes $0, \dots, n-1$ whose lists terminate, and let $t$ be a natural number with
$n \le 2^t$. Then after $t$ rounds of pointer jumping from the initial state, the distance of
every node $v$ is the rank of $v$. -/
theorem rounds_dist (hs : Terminates succ) {t : ℕ} (ht : n ≤ 2 ^ t) (v : Fin n) :
    (rounds succ t).dist v = rank hs v := by
  rw [(rounds_spec hs t v).2]
  have := rank_lt hs v
  omega

/-! ## Tabulated rounds -/

/-- **Tabulating a list-ranking state.** The tabulation of a pointer-jumping state $s$ on the
nodes $0, \dots, n - 1$ is the pair of arrays of length $n$ whose entries at $v$ are the pointer
and the distance of $v$ in $s$.

Evaluating the state after $t$ rounds directly re-reads earlier rounds' pointers at every query,
a cost growing exponentially with the number of rounds; the tabulated rounds cost $O(n)$ array
operations each. -/
def tabulate (s : State n) : Array (Option (Fin n)) × Array ℕ :=
  (Array.ofFn s.ptr, Array.ofFn s.dist)

/-- **One pointer-jumping round on arrays.** Given an array $P$ of pointers (each a node among
$0, \dots, n-1$ or undefined) and an array $D$ of natural-number distances, one round returns
arrays $P'$ and $D'$ of length $n$ where, for each node $v$, $P'[v]$ is $P[u]$ if $P[v] = u$ and is
undefined if $P[v]$ is undefined, and $D'[v] = D[v] + D[u]$ if $P[v] = u$ and $D'[v] = D[v]$ if
$P[v]$ is undefined. Entries missing from the input arrays are read as undefined pointers and
distance $0$. -/
def roundTab (s : Array (Option (Fin n)) × Array ℕ) : Array (Option (Fin n)) × Array ℕ :=
  (Array.ofFn fun v : Fin n => (s.1.getD v none).bind fun u => s.1.getD u none,
    Array.ofFn fun v : Fin n =>
      match s.1.getD v none with
      | none => s.2.getD v 0
      | some u => s.2.getD v 0 + s.2.getD u 0)

/-- **List-ranking rounds on arrays.** For a successor function $\mathrm{succ}$ on the nodes
$0, \dots, n - 1$ and $t \ge 0$, the arrays after $t$ rounds are a pair of arrays (pointers and
distances) defined by recursion on $t$: after $0$ rounds they are the tabulation of the initial
state of $\mathrm{succ}$, and after $t + 1$ rounds they are one round on arrays applied to the
arrays after $t$ rounds. -/
def roundsTab (succ : Fin n → Option (Fin n)) : ℕ → Array (Option (Fin n)) × Array ℕ
  | 0 => tabulate (init succ)
  | t + 1 => roundTab (roundsTab succ t)

private theorem getD_ofFn {α : Type*} (f : Fin n → α) (v : Fin n) (d : α) :
    (Array.ofFn f).getD v d = f v := by
  simp [v.isLt]

theorem roundTab_tabulate (s : State n) : roundTab (tabulate s) = tabulate (round s) := by
  simp only [roundTab, tabulate, round, getD_ofFn]

theorem roundsTab_eq (succ : Fin n → Option (Fin n)) :
    ∀ t, roundsTab succ t = tabulate (rounds succ t)
  | 0 => rfl
  | t + 1 => by rw [roundsTab, roundsTab_eq succ t, roundTab_tabulate]; rfl

/-- **List ranking by pointer jumping.** For a successor map $\mathrm{succ}$ on the nodes
$0, \dots, n-1$, list ranking by pointer jumping runs $\lceil \log_2 n \rceil$ rounds of pointer
jumping on arrays, starting from the initial state, and returns the resulting array of distances,
whose entry $v$ is the distance of node $v$.

When the lists terminate, entry $v$ is the rank of node $v$. -/
def listRanks (succ : Fin n → Option (Fin n)) : Array ℕ := (roundsTab succ (Nat.clog 2 n)).2

theorem size_listRanks (succ : Fin n → Option (Fin n)) : (listRanks succ).size = n := by
  rw [listRanks, roundsTab_eq, tabulate, Array.size_ofFn]

/-- **Pointer jumping ranks every list in ⌈log₂ n⌉ rounds.** Let $\mathrm{succ}$ be a successor map
on the nodes $0, \dots, n-1$ whose lists terminate. Then for every node $v$, entry $v$ of the table
returned by list ranking by pointer jumping, which runs $\lceil \log_2 n \rceil$ rounds, is the
rank of $v$. -/
theorem listRanks_getD (hs : Terminates succ) (v : Fin n) :
    (listRanks succ).getD v 0 = rank hs v := by
  rw [listRanks, roundsTab_eq, tabulate, getD_ofFn]
  exact rounds_dist hs (Nat.le_pow_clog (by decide) n) v

end Cslib.Algorithms.Lean.Parallel.ListRanking
