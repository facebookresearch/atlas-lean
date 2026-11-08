/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chang-Roberts leader election
-/
module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Basic

/-!
# Chang-Roberts leader election elects only the maximum

The Chang-Roberts algorithm (E. Chang and R. Roberts, *An improved algorithm
for decentralized extrema-finding in circular configurations of processes*,
CACM 22(5), 1979) on a unidirectional ring of `n + 1` processes `Fin (n + 1)`
with identifiers `id`, as a labelled transition system with FIFO channels. The
algorithm assumes distinct identifiers; the safety theorems below do not need
that assumption (messages carry the index of their origin), but with two equal
maximal identifiers nobody is ever elected, so election needs a unique
maximum.

Every process starts by sending its identifier to its successor. A process
receiving the identifier of process `j` forwards it if `id j` is larger than
its own, discards it if smaller, and declares itself leader if it is its own.
Messages carry the index of the originating process.

* `inv_reachable`: in every reachable state, a message from `j` waiting at
  process `k` has passed only processes with identifiers smaller than `id j`,
  and a leader's identifier is larger than every other.
* `leader_max`: a leader has the strictly largest identifier;
  `leader_unique`: there is at most one leader.

Only safety is proved: these results do not show that a leader is ever
elected. That the maximum is eventually elected needs distinct identifiers (or
a unique maximum) and a fairness assumption on message delivery, which are not
formalized here; a test shows an election on a three-process ring.
-/

@[expose] public section

namespace Cslib.Distributed.ChangRoberts

variable {n : ℕ}

/-- Global states: the FIFO channel into each process (holding the origins of
the identifiers in transit) and the processes that have declared themselves
leader. -/
structure State (n : ℕ) where
  /-- Messages waiting at each process, oldest first. -/
  chan : Fin (n + 1) → List (Fin (n + 1))
  /-- Whether each process has declared itself leader. -/
  leader : Fin (n + 1) → Bool

/-- The successor on the ring. -/
def succ (k : Fin (n + 1)) : Fin (n + 1) :=
  if h : k.val + 1 < n + 1 then ⟨k.val + 1, h⟩ else ⟨0, Nat.succ_pos n⟩

/-- The predecessor on the ring. -/
def pred (k : Fin (n + 1)) : Fin (n + 1) :=
  if k.val = 0 then ⟨n, Nat.lt_succ_self n⟩ else ⟨k.val - 1, by omega⟩

/-- Process `k` receives the oldest message in its channel: forward a larger
identifier, discard a smaller one, become leader on its own. -/
def deliver (id : Fin (n + 1) → ℕ) (s : State n) (k : Fin (n + 1)) : Option (State n) :=
  match s.chan k with
  | [] => none
  | j :: rest =>
      let c := Function.update s.chan k rest
      if id k < id j then
        some ⟨Function.update c (succ k) (c (succ k) ++ [j]), s.leader⟩
      else if j = k then
        some ⟨c, Function.update s.leader k true⟩
      else
        some ⟨c, s.leader⟩

/-- The algorithm as a labelled transition system; the label is the receiving
process. -/
def lts (id : Fin (n + 1) → ℕ) : LTS (State n) (Fin (n + 1)) where
  Tr s k t := deliver id s k = some t

/-- The initial state: every process has sent its identifier to its successor,
and nobody is leader. -/
def initial : State n := ⟨fun k => [pred k], fun _ => false⟩

/-- The states reachable from the initial state, by upstream `LTS.CanReach`
(a multistep transition `LTS.MTr` along some delivery schedule). -/
def Reachable (id : Fin (n + 1) → ℕ) (s : State n) : Prop := (lts id).CanReach initial s

theorem reachable_initial (id : Fin (n + 1) → ℕ) : Reachable id (initial : State n) :=
  ⟨[], .refl⟩

/-- The distance from `j` to `m` going around the ring, in `[0, n]`. -/
def gap (j m : Fin (n + 1)) : ℕ :=
  if j.val ≤ m.val then m.val - j.val else m.val + (n + 1) - j.val

/-- A message from `j` waiting at `k` has travelled `gap j k` links, or the
whole ring when it is back at `j`. -/
def travelled (j k : Fin (n + 1)) : ℕ := if k = j then n + 1 else gap j k

/-- The invariant: every process strictly between the origin of a message and
its current position has a smaller identifier, and a leader's identifier is
larger than every other. -/
structure Inv (id : Fin (n + 1) → ℕ) (s : State n) : Prop where
  msg : ∀ k j, j ∈ s.chan k → ∀ m, m ≠ j → gap j m < travelled j k → id m < id j
  leader : ∀ i, s.leader i = true → ∀ m, m ≠ i → id m < id i

theorem gap_le (j m : Fin (n + 1)) : gap j m ≤ n := by
  have := j.isLt; have := m.isLt
  unfold gap; split <;> omega

theorem eq_of_gap_eq {j m m' : Fin (n + 1)} (h : gap j m = gap j m') : m = m' := by
  have := j.isLt; have := m.isLt; have := m'.isLt
  unfold gap at h
  apply Fin.ext
  split at h <;> split at h <;> omega

theorem eq_of_gap_eq_zero {j m : Fin (n + 1)} (h : gap j m = 0) : m = j :=
  eq_of_gap_eq (h.trans (by simp [gap]))

/-- One more link: forwarding from `k ≠ j` adds one to the distance
travelled. -/
theorem travelled_succ {j k : Fin (n + 1)} (hk : k ≠ j) :
    travelled j (succ k) = gap j k + 1 := by
  have := j.isLt; have := k.isLt
  have hk' : k.val ≠ j.val := fun h => hk (Fin.ext h)
  unfold travelled gap succ
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;>
    simp only [Fin.ext_iff] at * <;> omega

/-- The initial message at `k` has travelled one link. -/
theorem travelled_pred (k : Fin (n + 1)) : travelled (pred k) k = 1 := by
  have hk := k.isLt
  by_cases hk0 : k.val = 0
  · have hp : pred k = ⟨n, Nat.lt_succ_self n⟩ := by simp [pred, hk0]
    rw [hp]
    unfold travelled gap
    split_ifs with h1 h2 <;> simp only [Fin.ext_iff] at * <;> omega
  · have hp : pred k = ⟨k.val - 1, by omega⟩ := by simp [pred, hk0]
    rw [hp]
    unfold travelled gap
    split_ifs with h1 h2 <;> simp only [Fin.ext_iff] at * <;> omega

theorem inv_initial (id : Fin (n + 1) → ℕ) : Inv id (initial : State n) := by
  refine ⟨fun k j hj m hm hgap => ?_, fun i hi => by simp [initial] at hi⟩
  simp only [initial, List.mem_singleton] at hj
  subst hj
  rw [travelled_pred] at hgap
  exact absurd (eq_of_gap_eq_zero (Nat.lt_one_iff.mp hgap)) hm

theorem inv_step {id : Fin (n + 1) → ℕ} {s t : State n} {k : Fin (n + 1)} (hs : Inv id s)
    (h : deliver id s k = some t) : Inv id t := by
  unfold deliver at h
  split at h
  · simp at h
  · rename_i j rest hchan
    have hjk : j ∈ s.chan k := by rw [hchan]; simp
    have hrest : ∀ x, x ∈ rest → x ∈ s.chan k := fun x hx => by rw [hchan]; simp [hx]
    -- messages of the channels after removing the head
    have hc : ∀ k' x, x ∈ Function.update s.chan k rest k' → x ∈ s.chan k' := by
      intro k' x hx
      by_cases hk' : k' = k
      · subst hk'; rw [Function.update_self] at hx; exact hrest x hx
      · rwa [Function.update_of_ne hk'] at hx
    split_ifs at h with hlt heq
    · -- forward
      obtain rfl := Option.some.inj h
      have hjne : j ≠ k := fun he => by rw [he] at hlt; exact lt_irrefl _ hlt
      refine ⟨fun k' x hx m hm hgap => ?_, hs.leader⟩
      dsimp only at hx
      by_cases hk' : k' = succ k
      · subst hk'
        rw [Function.update_self, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hs.msg _ x (hc _ x hx) m hm hgap
        · rw [travelled_succ (Ne.symm hjne)] at hgap
          rcases Nat.lt_succ_iff_lt_or_eq.mp hgap with hlt' | heq'
          · have ht : travelled x k = gap x k := by simp [travelled, Ne.symm hjne]
            exact hs.msg k x hjk m hm (ht ▸ hlt')
          · rw [eq_of_gap_eq heq']; exact hlt
      · rw [Function.update_of_ne hk'] at hx
        exact hs.msg k' x (hc k' x hx) m hm hgap
    · -- own identifier: become leader
      obtain rfl := Option.some.inj h
      subst heq
      refine ⟨fun k' x hx m hm hgap => hs.msg k' x (hc k' x hx) m hm hgap, fun i hi m hm => ?_⟩
      dsimp only at hi
      by_cases hi' : i = j
      · subst hi'
        have ht : travelled i i = n + 1 := by simp [travelled]
        exact hs.msg i i hjk m hm (ht ▸ Nat.lt_succ_of_le (gap_le _ _))
      · rw [Function.update_of_ne hi'] at hi
        exact hs.leader i hi m hm
    · -- discard
      obtain rfl := Option.some.inj h
      exact ⟨fun k' x hx m hm hgap => hs.msg k' x (hc k' x hx) m hm hgap, hs.leader⟩

/-- Multistep transitions preserve the invariant. -/
theorem inv_mtr {id : Fin (n + 1) → ℕ} {s t : State n} {ks : List (Fin (n + 1))}
    (hm : (lts id).MTr s ks t) (hs : Inv id s) : Inv id t := by
  induction hm with
  | refl => exact hs
  | stepL htr _ ih => exact ih (inv_step hs htr)

/-- The invariant holds in every reachable state. -/
theorem inv_reachable {id : Fin (n + 1) → ℕ} {s : State n} (h : Reachable id s) : Inv id s :=
  let ⟨_, hm⟩ := h
  inv_mtr hm (inv_initial id)

/-- **Only the maximum is elected**: a leader's identifier is larger than every
other process's. -/
theorem leader_max {id : Fin (n + 1) → ℕ} {s : State n} (h : Reachable id s) {i : Fin (n + 1)}
    (hi : s.leader i = true) {m : Fin (n + 1)} (hm : m ≠ i) : id m < id i :=
  (inv_reachable h).leader i hi m hm

/-- **There is at most one leader.** -/
theorem leader_unique {id : Fin (n + 1) → ℕ} {s : State n} (h : Reachable id s)
    {i i' : Fin (n + 1)} (hi : s.leader i = true) (hi' : s.leader i' = true) : i = i' := by
  by_contra hne
  exact lt_asymm (leader_max h hi (Ne.symm hne)) (leader_max h hi' hne)

/-- Deliver a sequence of messages, failing on an empty channel. -/
def run (id : Fin (n + 1) → ℕ) : State n → List (Fin (n + 1)) → Option (State n)
  | s, [] => some s
  | s, k :: ks => (deliver id s k).bind fun t => run id t ks

/-- Running a schedule is exactly a multistep transition along it. -/
theorem run_eq_some_iff {id : Fin (n + 1) → ℕ} :
    ∀ {s t : State n} {ks : List (Fin (n + 1))}, run id s ks = some t ↔ (lts id).MTr s ks t
  | s, t, [] => by simp [run]
  | s, t, k :: ks => by
      rw [LTS.MTr.cons_iff]
      simp only [run]
      cases hd : deliver id s k with
      | none =>
          simp only [Option.bind_none, reduceCtorEq, false_iff, not_exists, not_and]
          intro u hu
          exact absurd (hu.symm.trans hd) (by simp)
      | some u =>
          simp only [Option.bind_some]
          rw [run_eq_some_iff]
          constructor
          · exact fun hm => ⟨u, hd, hm⟩
          · rintro ⟨u', hu', hm⟩
            have : u = u' := Option.some.inj (hd.symm.trans hu')
            exact this ▸ hm

theorem reachable_of_run {id : Fin (n + 1) → ℕ} {s t : State n} (ks : List (Fin (n + 1)))
    (hs : Reachable id s) (h : run id s ks = some t) : Reachable id t :=
  let ⟨ks₀, hm⟩ := hs
  ⟨ks₀ ++ ks, LTS.MTr.comp _ hm (run_eq_some_iff.mp h)⟩

end Cslib.Distributed.ChangRoberts
