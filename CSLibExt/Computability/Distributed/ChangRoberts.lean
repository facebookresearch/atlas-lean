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

/-- **Chang–Roberts global states.** For a ring of $n + 1$ processes $0, \dots, n$, a global
state assigns to each process $k$ the FIFO channel of messages waiting at $k$, oldest first,
where each message is the index of the process whose identifier it carries, and records for
each process whether it has declared itself leader. -/
structure State (n : ℕ) where
  /-- Messages waiting at each process, oldest first. -/
  chan : Fin (n + 1) → List (Fin (n + 1))
  /-- Whether each process has declared itself leader. -/
  leader : Fin (n + 1) → Bool

/-- **Successor on the Chang–Roberts ring.** On the ring of $n + 1$ processes $0, \dots, n$, the
successor of process $k$ is $k + 1$ when $k < n$, and $0$ when $k = n$. -/
def succ (k : Fin (n + 1)) : Fin (n + 1) :=
  if h : k.val + 1 < n + 1 then ⟨k.val + 1, h⟩ else ⟨0, Nat.succ_pos n⟩

/-- **Predecessor on the ring.** On a ring of $n + 1$ processes numbered $0, \dots, n$, the
predecessor of $k$ is $k - 1$ if $k \ne 0$, and $n$ if $k = 0$. -/
def pred (k : Fin (n + 1)) : Fin (n + 1) :=
  if k.val = 0 then ⟨n, Nat.lt_succ_self n⟩ else ⟨k.val - 1, by omega⟩

/-- **Delivering a message in the Chang–Roberts ring.** On a ring of $n + 1$ processes with
identifiers $\mathrm{id}$, process $k$ receives the oldest message in its channel in state $s$.
If the channel of $k$ is empty there is no step. Otherwise let $j$ be the origin of that message,
which is removed from the channel: if $\mathrm{id}(k) < \mathrm{id}(j)$, process $k$ forwards it
by appending $j$ to the end of the channel of its successor on the ring; otherwise, if $j = k$,
process $k$ declares itself leader; otherwise the message is discarded. Nothing else changes. -/
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

/-- **The Chang–Roberts transition system.** For identifiers $\mathrm{id}$, the algorithm is the
labelled transition system whose states are the global states and whose labels are processes:
there is a transition from $s$ to $t$ labelled $k$ exactly when delivering the oldest message in
the channel of process $k$ in state $s$ gives $t$. -/
def lts (id : Fin (n + 1) → ℕ) : LTS (State n) (Fin (n + 1)) where
  Tr s k t := deliver id s k = some t

/-- **Initial state of the Chang–Roberts ring.** In the initial state the channel into each
process $k$ holds exactly one message, whose origin is the predecessor of $k$ on the ring (so
every process has sent its identifier to its successor), and no process is leader. -/
def initial : State n := ⟨fun k => [pred k], fun _ => false⟩

/-- **Reachable states of Chang–Roberts.** Given a natural-number identifier $\mathrm{id}(k)$ for
each process $k$ of the ring of $n + 1$ processes, a global state $s$ is reachable when the
Chang–Roberts transition system with these identifiers leads from the initial state to $s$ by a
multistep transition along some finite list of labels, that is, of receiving processes. -/
def Reachable (id : Fin (n + 1) → ℕ) (s : State n) : Prop := (lts id).CanReach initial s

theorem reachable_initial (id : Fin (n + 1) → ℕ) : Reachable id (initial : State n) :=
  ⟨[], .refl⟩

/-- **Forward distance on the ring.** For processes $j$ and $m$ on a ring of $n + 1$ processes
numbered $0, \dots, n$, the gap from $j$ to $m$ is the number of successor steps from $j$ to
$m$: it is $m - j$ if $j \le m$, and $m + (n + 1) - j$ otherwise. It lies in $[0, n]$. -/
def gap (j m : Fin (n + 1)) : ℕ :=
  if j.val ≤ m.val then m.val - j.val else m.val + (n + 1) - j.val

/-- **Distance travelled by a message.** For processes $j, k$ of the ring of $n + 1$ processes,
the distance travelled by a message from $j$ waiting at $k$ is $n + 1$, the whole ring, when
$k = j$, and otherwise the ring distance from $j$ to $k$, the number of links from $j$ forward
to $k$. -/
def travelled (j k : Fin (n + 1)) : ℕ := if k = j then n + 1 else gap j k

/-- **The Chang–Roberts invariant.** Given identifiers $\mathrm{id}$ on a ring of $n + 1$
processes, a state satisfies the invariant when two conditions hold. First, for every message
from origin $j$ waiting in the channel of process $k$, every process $m \ne j$ that the message
has already passed has a smaller identifier, $\mathrm{id}(m) < \mathrm{id}(j)$; here $m$ has been
passed when its forward distance from $j$ is less than the distance the message has travelled,
which is the forward distance from $j$ to $k$ if $k \ne j$, and $n + 1$ (the whole ring) if
$k = j$. Second, for every leader $i$ and every process $m \ne i$, we have
$\mathrm{id}(m) < \mathrm{id}(i)$. -/
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

/-- **Forwarding adds one link.** For processes $j$ and $k$ of the ring with $k \ne j$, the
distance travelled by a message from $j$ waiting at the successor of $k$ is the number of links
from $j$ forward to $k$, plus one. -/
theorem travelled_succ {j k : Fin (n + 1)} (hk : k ≠ j) :
    travelled j (succ k) = gap j k + 1 := by
  have := j.isLt; have := k.isLt
  have hk' : k.val ≠ j.val := fun h => hk (Fin.ext h)
  unfold travelled gap succ
  split_ifs with h1 h2 h3 h4 h5 h6 h7 <;>
    simp only [Fin.ext_iff] at * <;> omega

/-- **The initial messages have travelled one link.** For every process $k$ of the ring, the
distance travelled by a message from the predecessor of $k$ waiting at $k$ is $1$. -/
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

/-- **The Chang–Roberts invariant is preserved along runs.** For every assignment of identifiers,
if the invariant holds in a state $s$ and the state $t$ is reached from $s$ by delivering messages
along some schedule of receiving processes (a multistep transition of the algorithm's labelled
transition system), then the invariant holds in $t$. -/
theorem inv_mtr {id : Fin (n + 1) → ℕ} {s t : State n} {ks : List (Fin (n + 1))}
    (hm : (lts id).MTr s ks t) (hs : Inv id s) : Inv id t := by
  induction hm with
  | refl => exact hs
  | stepL htr _ ih => exact ih (inv_step hs htr)

/-- **The Chang–Roberts invariant holds in every reachable state.** For every assignment of
identifiers, every state reachable from the initial state satisfies the invariant. -/
theorem inv_reachable {id : Fin (n + 1) → ℕ} {s : State n} (h : Reachable id s) : Inv id s :=
  let ⟨_, hm⟩ := h
  inv_mtr hm (inv_initial id)

/-- **Only the maximum is elected.** Let $\mathrm{id}$ assign a natural-number identifier, not
necessarily distinct, to each process $0, \dots, n$ of the Chang–Roberts ring. In every state
reachable with these identifiers, if process $i$ has declared itself leader, then
$\mathrm{id}(m) < \mathrm{id}(i)$ for every process $m \ne i$. -/
theorem leader_max {id : Fin (n + 1) → ℕ} {s : State n} (h : Reachable id s) {i : Fin (n + 1)}
    (hi : s.leader i = true) {m : Fin (n + 1)} (hm : m ≠ i) : id m < id i :=
  (inv_reachable h).leader i hi m hm

/-- **There is at most one leader.** In every state of the Chang–Roberts algorithm reachable from
the initial state, any two processes that have declared themselves leader are equal. -/
theorem leader_unique {id : Fin (n + 1) → ℕ} {s : State n} (h : Reachable id s)
    {i i' : Fin (n + 1)} (hi : s.leader i = true) (hi' : s.leader i' = true) : i = i' := by
  by_contra hne
  exact lt_asymm (leader_max h hi (Ne.symm hne)) (leader_max h hi' hne)

/-- **Running a delivery schedule.** Given a natural-number identifier $\mathrm{id}(k)$ for each
process $k$ of the ring, a global state $s$ and a list $k_1, \dots, k_r$ of processes, the run
applies the Chang–Roberts delivery step at $k_1$, then at $k_2$, and so on. It returns the final
state, or no state as soon as some $k_i$ has an empty channel at its turn; on the empty list it
returns $s$. -/
def run (id : Fin (n + 1) → ℕ) : State n → List (Fin (n + 1)) → Option (State n)
  | s, [] => some s
  | s, k :: ks => (deliver id s k).bind fun t => run id t ks

/-- **Runs are multistep transitions.** Given a natural-number identifier $\mathrm{id}(k)$ for
each process $k$ of the ring, for all global states $s, t$ and every list $\kappa$ of processes,
running the schedule $\kappa$ from $s$ returns $t$ if and only if the Chang–Roberts transition
system with identifiers $\mathrm{id}$ has a multistep transition from $s$ to $t$ labelled by
$\kappa$. -/
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
