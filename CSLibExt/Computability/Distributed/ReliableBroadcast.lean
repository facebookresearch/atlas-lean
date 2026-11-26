/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.FailureDetector
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.AddSub

/-!
# Reliable broadcast

Reliable broadcast in asynchronous systems with crash failures, after Chandra and Toueg, and its
implementation by diffusion.

## Specification

Reliable broadcast is given by two primitives, R-broadcast and R-deliver. Messages range over
any type with a map giving the sender of each message. A run is recorded by the set of its
correct processes and, at each time, its R-broadcast or R-deliver event, if any.
`IsReliableBroadcast` asks for validity, agreement and uniform integrity. In the source, every
message carries its sender and a sequence number, which make it unique; the specification does
not assume this, and the diffusion algorithm below ensures it.

## Diffusion

* **Processes and messages:** any type `P` of processes. A process numbers the messages it
  R-broadcasts `0, 1, 2, …`, so no message is R-broadcast twice.
* **Channels:** for every ordered pair `q, p` of processes, the channel from `q` to `p` is the
  multiset of copies of messages that `q` has sent to `p` and `p` has not yet received. A process
  receives only copies that are in a channel to it, and each copy at most once.
* **Algorithm** (Chandra and Toueg, Figure 4): to R-broadcast `m`, a process sends `m` to every
  process, itself included. When a process receives `m` for the first time, it sends `m` to every
  process unless it is the sender of `m`, and then R-delivers `m`. A later copy of `m` is
  discarded.
* **Crashes:** a process crashes at any time and then takes no step. It may crash while it sends
  a message to every process: it has then sent copies only to the processes of some finite set,
  and, when it was relaying the message, it does not R-deliver it.
* **Runs:** infinite executions of the transition system `Diffusion.lts` from `Diffusion.init`,
  in which a step may also leave the state unchanged. A process is correct if it never crashes.
* **Fairness** (reliable channels): every copy of a message in a channel to a correct process is
  eventually received.

## Main definitions

* `IsReliableBroadcast`: the specification of reliable broadcast.
* `Diffusion.lts`, `Diffusion.correct`, `Diffusion.ReliableDelivery`: the diffusion algorithm,
  the correct processes of a run, and fairness.

## Main results

* `diffusion_isReliableBroadcast`: every fair run of the diffusion algorithm satisfies validity,
  agreement and uniform integrity.
* `Diffusion.exists_failurePattern`: with finitely many processes, one of them correct, the
  crashed sets of a run form a failure pattern (`FailureDetector.FailurePattern`) with the same
  correct processes.

## References

* T. D. Chandra and S. Toueg, *Unreliable failure detectors for reliable distributed systems*,
  Journal of the ACM 43(2), 1996, 225–267: Section 2 (the model: reliable channels, crash
  failures in Section 2.1, steps and runs in Section 2.5), Section 4 (reliable broadcast) and
  Figure 4 (diffusion).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.ReliableBroadcast

-- An event of reliable broadcast: `broadcast p m` when process `p` R-broadcasts `m`, and
-- `deliver p m` when `p` R-delivers `m`.
inductive Event (P M : Type*) where
  | broadcast (p : P) (m : M)
  | deliver (p : P) (m : M)

variable {P M D : Type*}

/-- **Reliable broadcast.** Messages range over a type `M`, and `sender m` is the process that
sends the message `m`. A run of a system of processes `P` is recorded by the set `correct` of its
correct processes and by its events: `ev t` is the event of the run at time `t`, if any, where
`Event.broadcast p m` says that process `p` R-broadcasts the message `m` and `Event.deliver p m`
says that `p` R-delivers `m`. The run satisfies reliable broadcast if it has the following
properties.

* Validity: if a correct process `p` R-broadcasts `m` at time `t`, then `p` R-delivers `m` at some
  time `t' ≥ t`.
* Agreement: if a correct process R-delivers `m`, then every correct process R-delivers `m` at
  some time.
* Uniform integrity: every process `p`, correct or not, R-delivers each message `m` at most once,
  and only at a time `t` such that `sender m` R-broadcasts `m` at some time `t' < t`. -/
structure IsReliableBroadcast (sender : M → P) (correct : Set P) (ev : ℕ → Option (Event P M)) :
    Prop where
  /-- A correct process R-delivers every message it R-broadcasts, at that time or later. -/
  validity : ∀ p ∈ correct, ∀ m t, ev t = some (.broadcast p m) →
    ∃ t', t ≤ t' ∧ ev t' = some (.deliver p m)
  /-- A message R-delivered by a correct process is R-delivered by every correct process. -/
  agreement : ∀ p ∈ correct, ∀ m t, ev t = some (.deliver p m) →
    ∀ q ∈ correct, ∃ t', ev t' = some (.deliver q m)
  /-- Every process R-delivers a message at most once, and only after its sender R-broadcasts
  it. -/
  uniformIntegrity : ∀ p m t, ev t = some (.deliver p m) →
    (∀ t', ev t' = some (.deliver p m) → t' = t) ∧
      ∃ t' < t, ev t' = some (.broadcast (sender m) m)

namespace Diffusion

-- A message of the diffusion algorithm carries the identity of its sender, the sequence number
-- its sender gives it and a payload.
structure Message (P D : Type*) where
  /-- The process that R-broadcasts the message. -/
  sender : P
  /-- The sequence number of the message among those of its sender. -/
  seq : ℕ
  /-- The contents of the message. -/
  payload : D
deriving DecidableEq


-- The state of the diffusion algorithm.
structure State (P D : Type*) where
  /-- The processes that have crashed. -/
  crashed : Set P
  /-- The sequence number that each process gives the next message it R-broadcasts. -/
  nextSeq : P → ℕ
  /-- The messages that each process has received, and so R-delivered. -/
  delivered : P → Set (Message P D)
  /-- `chan q p` is the multiset of copies of messages that `q` has sent to `p` and that `p` has
  not yet received. -/
  chan : P → P → Multiset (Message P D)

-- The initial state: no process has crashed, R-broadcast or received anything, and every channel
-- is empty.
def init : State P D where
  crashed := ∅
  nextSeq _ := 0
  delivered _ := ∅
  chan _ _ := 0

-- The steps of the diffusion algorithm. In `broadcast p m cut`, process `p` R-broadcasts `m`; in
-- `deliver p q m cut`, it receives `m` from `q` for the first time and relays it; in each, `cut`
-- is `none` if the step completes, and `some S` if `p` crashes during the step, after sending
-- `m` to the processes of `S` only. In `discard p q m`, `p` receives from `q` a copy of `m`
-- that it has already received; in `crash p`, `p` crashes; `idle` changes nothing.
inductive Step (P D : Type*) where
  | broadcast (p : P) (m : Message P D) (cut : Option (Finset P))
  | deliver (p q : P) (m : Message P D) (cut : Option (Finset P))
  | discard (p q : P) (m : Message P D)
  | crash (p : P)
  | idle

-- The R-broadcast or R-deliver event of a step, if any: a step that crashes while relaying a
-- message does not R-deliver it.
def Step.event : Step P D → Option (Event P (Message P D))
  | .broadcast p m _ => some (.broadcast p m)
  | .deliver p _ m none => some (.deliver p m)
  | _ => none

-- `μ.Receives p q m`: the step `μ` is a receipt, by `p`, of a copy of `m` from the channel from
-- `q` to `p`.
def Step.Receives (p q : P) (m : Message P D) : Step P D → Prop
  | .deliver p' q' m' _ => p' = p ∧ q' = q ∧ m' = m
  | .discard p' q' m' => p' = p ∧ q' = q ∧ m' = m
  | _ => False

variable [DecidableEq P] [DecidableEq D]

-- The channels `c` after process `p` sends a copy of `m` to every process, if `cut = none`, or
-- to the processes of `S`, if `cut = some S`.
def send (c : P → P → Multiset (Message P D)) (p : P) (m : Message P D)
    (cut : Option (Finset P)) : P → P → Multiset (Message P D) :=
  fun a b => if a = p ∧ cut.all (fun S => decide (b ∈ S)) = true then m ::ₘ c a b else c a b

-- The channels `c` after process `p` receives a copy of `m` from the channel from `q`.
def take (c : P → P → Multiset (Message P D)) (q p : P) (m : Message P D) :
    P → P → Multiset (Message P D) :=
  fun a b => if a = q ∧ b = p then (c a b).erase m else c a b

-- The transition system of the diffusion algorithm. A process takes a step only if it has not
-- crashed. It R-broadcasts only messages whose sender it is, with its next sequence number. It
-- receives only a copy that is in a channel to it, and relays it only if it is not its sender.
def lts : LTS (State P D) (Step P D) where
  Tr s μ s' := match μ with
    | .broadcast p m cut =>
      p ∉ s.crashed ∧ m.sender = p ∧ m.seq = s.nextSeq p ∧
        s' = { crashed := if cut.isSome then insert p s.crashed else s.crashed
               nextSeq := Function.update s.nextSeq p (s.nextSeq p + 1)
               delivered := s.delivered
               chan := send s.chan p m cut }
    | .deliver p q m cut =>
      p ∉ s.crashed ∧ m ∈ s.chan q p ∧ m ∉ s.delivered p ∧
        s' = { crashed := if cut.isSome then insert p s.crashed else s.crashed
               nextSeq := s.nextSeq
               delivered := if cut.isSome then s.delivered
                 else Function.update s.delivered p (insert m (s.delivered p))
               chan := if m.sender = p then take s.chan q p m
                 else send (take s.chan q p m) p m cut }
    | .discard p q m =>
      p ∉ s.crashed ∧ m ∈ s.chan q p ∧ m ∈ s.delivered p ∧
        s' = { s with chan := take s.chan q p m }
    | .crash p => p ∉ s.crashed ∧ s' = { s with crashed := insert p s.crashed }
    | .idle => s' = s

-- The correct processes of a sequence of states: those that never crash.
def correct (ss : ωSequence (State P D)) : Set P :=
  {p | ∀ t, p ∉ (ss t).crashed}

-- Fairness, or reliable channels: whenever a copy of `m` is in the channel from `q` to a correct
-- process `p`, then `p` receives a copy of `m` from that channel at that time or later.
def ReliableDelivery (ss : ωSequence (State P D)) (μs : ωSequence (Step P D)) : Prop :=
  ∀ p ∈ correct ss, ∀ q m t, m ∈ (ss t).chan q p → ∃ t', t ≤ t' ∧ (μs t').Receives p q m

/-! ### Single steps -/

omit [DecidableEq P] [DecidableEq D] in
private theorem event_eq_broadcast {μ : Step P D} {p : P} {m : Message P D} :
    μ.event = some (.broadcast p m) ↔ ∃ cut, μ = .broadcast p m cut := by
  cases μ with
  | deliver p' q' m' cut => cases cut <;> simp [Step.event]
  | _ => simp [Step.event]

omit [DecidableEq P] [DecidableEq D] in
private theorem event_eq_deliver {μ : Step P D} {p : P} {m : Message P D} :
    μ.event = some (.deliver p m) ↔ ∃ q, μ = .deliver p q m none := by
  cases μ with
  | deliver p' q' m' cut => cases cut <;> simp [Step.event, and_comm]
  | _ => simp [Step.event]

omit [DecidableEq D] in
private theorem mem_send {c : P → P → Multiset (Message P D)} {p a b : P}
    {m m' : Message P D} {cut : Option (Finset P)} (h : m ∈ send c p m' cut a b) :
    (a = p ∧ m = m') ∨ m ∈ c a b := by
  unfold send at h
  split_ifs at h with hc
  · rcases Multiset.mem_cons.1 h with rfl | h
    · exact .inl ⟨hc.1, rfl⟩
    · exact .inr h
  · exact .inr h

omit [DecidableEq D] in
private theorem mem_send_none (c : P → P → Multiset (Message P D)) (p b : P)
    (m : Message P D) : m ∈ send c p m none p b := by
  simp [send]

private theorem mem_take {c : P → P → Multiset (Message P D)} {q p a b : P}
    {m m' : Message P D} (h : m ∈ take c q p m' a b) : m ∈ c a b := by
  unfold take at h
  split_ifs at h
  · exact Multiset.mem_of_mem_erase h
  · exact h

private theorem crashed_subset {s s' : State P D} {μ : Step P D} (h : lts.Tr s μ s') :
    s.crashed ⊆ s'.crashed := by
  cases μ with
  | broadcast p m cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    dsimp only
    split_ifs <;> simp [Set.subset_insert]
  | deliver p q m cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    dsimp only
    split_ifs <;> simp [Set.subset_insert]
  | discard p q m =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact subset_rfl
  | crash p =>
    obtain ⟨-, rfl⟩ := h
    exact Set.subset_insert _ _
  | idle =>
    cases h
    exact subset_rfl

private theorem delivered_subset {s s' : State P D} {μ : Step P D} (h : lts.Tr s μ s')
    (p : P) : s.delivered p ⊆ s'.delivered p := by
  cases μ with
  | broadcast p' m cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact subset_rfl
  | deliver p' q m cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    dsimp only
    split_ifs
    · exact subset_rfl
    · by_cases hp : p = p'
      · subst hp
        simp [Set.subset_insert]
      · simp [Function.update_of_ne hp]
  | discard p' q m =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact subset_rfl
  | crash p' =>
    obtain ⟨-, rfl⟩ := h
    exact subset_rfl
  | idle =>
    cases h
    exact subset_rfl

private theorem nextSeq_le {s s' : State P D} {μ : Step P D} (h : lts.Tr s μ s') (p : P) :
    s.nextSeq p ≤ s'.nextSeq p := by
  cases μ with
  | broadcast p' m cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    by_cases hp : p = p'
    · subst hp
      simp
    · simp [Function.update_of_ne hp]
  | deliver p' q m cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact le_rfl
  | discard p' q m =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact le_rfl
  | crash p' =>
    obtain ⟨-, rfl⟩ := h
    exact le_rfl
  | idle =>
    cases h
    exact le_rfl

-- A message enters a delivered set only by a `deliver` step that completes.
private theorem mem_delivered_of_tr {s s' : State P D} {μ : Step P D} (h : lts.Tr s μ s')
    {p : P} {m : Message P D} (hm : m ∈ s'.delivered p) :
    m ∈ s.delivered p ∨ ∃ q, μ = .deliver p q m none ∧ m ∈ s.chan q p := by
  cases μ with
  | broadcast p' m' cut =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact .inl hm
  | deliver p' q m' cut =>
    obtain ⟨-, hc, -, rfl⟩ := h
    dsimp only at hm
    cases cut with
    | some S => exact .inl hm
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hm
      by_cases hp : p = p'
      · subst hp
        rcases (by simpa using hm : m = m' ∨ m ∈ s.delivered p) with rfl | hm
        · exact .inr ⟨q, rfl, hc⟩
        · exact .inl hm
      · exact .inl (by simpa [Function.update_of_ne hp] using hm)
  | discard p' q m' =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact .inl hm
  | crash p' =>
    obtain ⟨-, rfl⟩ := h
    exact .inl hm
  | idle =>
    cases h
    exact .inl hm

-- A copy of a message enters a channel from `a` only when `a` R-broadcasts it or relays it.
private theorem mem_chan_of_tr {s s' : State P D} {μ : Step P D} (h : lts.Tr s μ s')
    {a b : P} {m : Message P D} (hm : m ∈ s'.chan a b) :
    m ∈ s.chan a b ∨ (∃ cut, μ = .broadcast a m cut ∧ m.sender = a ∧ m.seq = s.nextSeq a) ∨
      ∃ q cut, μ = .deliver a q m cut ∧ m ∈ s.chan q a := by
  cases μ with
  | broadcast p m' cut =>
    obtain ⟨-, hs, hq, rfl⟩ := h
    rcases mem_send hm with ⟨rfl, rfl⟩ | hm
    · exact .inr (.inl ⟨cut, rfl, hs, hq⟩)
    · exact .inl hm
  | deliver p q m' cut =>
    obtain ⟨-, hc, -, rfl⟩ := h
    dsimp only at hm
    split_ifs at hm
    · exact .inl (mem_take hm)
    · rcases mem_send hm with ⟨rfl, rfl⟩ | hm
      · exact .inr (.inr ⟨q, cut, rfl, hc⟩)
      · exact .inl (mem_take hm)
  | discard p q m' =>
    obtain ⟨-, -, -, rfl⟩ := h
    exact .inl (mem_take hm)
  | crash p =>
    obtain ⟨-, rfl⟩ := h
    exact .inl hm
  | idle =>
    cases h
    exact .inl hm

/-! ### Runs -/

variable {ss : ωSequence (State P D)} {μs : ωSequence (Step P D)}

private theorem crashed_mono (hex : lts.OmegaExecution ss μs) {t t' : ℕ} (h : t ≤ t') :
    (ss t).crashed ⊆ (ss t').crashed := by
  induction t', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (crashed_subset (hex n))

-- With finitely many processes, one of them correct, the crashed sets of a run form a failure
-- pattern in the sense of Chandra and Toueg, whose correct processes are those of the run.
theorem exists_failurePattern [Finite P] (hex : lts.OmegaExecution ss μs)
    (h : (correct ss).Nonempty) :
    ∃ F : FailureDetector.FailurePattern P,
      (∀ t, F.crashedBy t = (ss t).crashed) ∧ F.correct = correct ss :=
  ⟨⟨fun t => (ss t).crashed, fun _ _ hle => crashed_mono hex hle, h⟩, fun _ => rfl, rfl⟩

private theorem delivered_mono (hex : lts.OmegaExecution ss μs) {t t' : ℕ} (h : t ≤ t')
    (p : P) : (ss t).delivered p ⊆ (ss t').delivered p := by
  induction t', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact ih.trans (delivered_subset (hex n) p)

private theorem nextSeq_mono (hex : lts.OmegaExecution ss μs) {t t' : ℕ} (h : t ≤ t')
    (p : P) : (ss t).nextSeq p ≤ (ss t').nextSeq p := by
  induction t', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (nextSeq_le (hex n) p)

-- A correct process does not crash during a step.
private theorem cut_eq_none_of_broadcast (hex : lts.OmegaExecution ss μs) {p : P}
    (hp : p ∈ correct ss) {t : ℕ} {m : Message P D} {cut : Option (Finset P)}
    (hμ : μs t = .broadcast p m cut) : cut = none := by
  have h := hex t
  rw [hμ] at h
  obtain ⟨-, -, -, hs⟩ := h
  cases cut with
  | none => rfl
  | some S =>
    refine absurd ?_ (hp (t + 1))
    simp [hs]

private theorem cut_eq_none_of_deliver (hex : lts.OmegaExecution ss μs) {p q : P}
    (hp : p ∈ correct ss) {t : ℕ} {m : Message P D} {cut : Option (Finset P)}
    (hμ : μs t = .deliver p q m cut) : cut = none := by
  have h := hex t
  rw [hμ] at h
  obtain ⟨-, -, -, hs⟩ := h
  cases cut with
  | none => rfl
  | some S =>
    refine absurd ?_ (hp (t + 1))
    simp [hs]

-- The first time a message is in a delivered set is just after a completed `deliver` step.
private theorem exists_deliver_of_mem (hex : lts.OmegaExecution ss μs) {p : P}
    {m : Message P D} {t₁ t₂ : ℕ} (h₁ : m ∉ (ss t₁).delivered p)
    (h₂ : m ∈ (ss t₂).delivered p) :
    ∃ t, t₁ ≤ t ∧ t < t₂ ∧ ∃ q, μs t = .deliver p q m none := by
  induction t₂ with
  | zero =>
    exact absurd (delivered_mono hex (Nat.zero_le t₁) p h₂) h₁
  | succ n ih =>
    rcases mem_delivered_of_tr (hex n) h₂ with h | ⟨q, hq, -⟩
    · obtain ⟨t, ht₁, ht₂, hμ⟩ := ih h
      exact ⟨t, ht₁, by omega, hμ⟩
    · refine ⟨n, ?_, by omega, q, hq⟩
      by_contra hn
      exact h₁ (delivered_mono hex (by omega) p h₂)

-- No creation: every copy in a channel is of a message that its sender has R-broadcast.
private theorem exists_broadcast_of_mem_chan (h0 : ss 0 = init)
    (hex : lts.OmegaExecution ss μs) {a b : P} {m : Message P D} {t : ℕ}
    (hm : m ∈ (ss t).chan a b) :
    ∃ t' < t, (μs t').event = some (.broadcast m.sender m) := by
  induction t generalizing a b with
  | zero => simp [h0, init] at hm
  | succ n ih =>
    rcases mem_chan_of_tr (hex n) hm with h | ⟨cut, hμ, hs, -⟩ | ⟨q, cut, -, h⟩
    · obtain ⟨t', ht', he⟩ := ih h
      exact ⟨t', by omega, he⟩
    · exact ⟨n, by omega, by rw [hμ, hs]; rfl⟩
    · obtain ⟨t', ht', he⟩ := ih h
      exact ⟨t', by omega, he⟩

-- Uniqueness: a message whose sequence number its sender has not yet used is nowhere.
private theorem not_mem_of_nextSeq_le (h0 : ss 0 = init) (hex : lts.OmegaExecution ss μs)
    {m : Message P D} {t : ℕ} (hle : (ss t).nextSeq m.sender ≤ m.seq) :
    (∀ a b, m ∉ (ss t).chan a b) ∧ ∀ p, m ∉ (ss t).delivered p := by
  induction t with
  | zero => simp [h0, init]
  | succ n ih =>
    obtain ⟨ihc, ihd⟩ := ih ((nextSeq_le (hex n) _).trans hle)
    refine ⟨fun a b hm => ?_, fun p hm => ?_⟩
    · rcases mem_chan_of_tr (hex n) hm with h | ⟨cut, hμ, hs, hq⟩ | ⟨q, cut, -, h⟩
      · exact ihc a b h
      · have h := hex n
        rw [hμ] at h
        obtain ⟨-, -, -, hss⟩ := h
        rw [hss, hs] at hle
        simp only [Function.update_self] at hle
        omega
      · exact ihc q a h
    · rcases mem_delivered_of_tr (hex n) hm with h | ⟨q, -, h⟩
      · exact ihd p h
      · exact ihc q p h

-- A correct process eventually holds in its delivered set every message in a channel to it.
private theorem exists_mem_delivered (hex : lts.OmegaExecution ss μs)
    (hfair : ReliableDelivery ss μs) {p q : P} (hp : p ∈ correct ss) {m : Message P D}
    {t : ℕ} (hm : m ∈ (ss t).chan q p) : ∃ T, m ∈ (ss T).delivered p := by
  obtain ⟨t', -, hr⟩ := hfair p hp q m t hm
  refine ⟨t' + 1, ?_⟩
  cases hμ : μs t' with
  | deliver p' q' m' cut =>
    rw [hμ] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    have hcut := cut_eq_none_of_deliver hex hp hμ
    subst hcut
    have h := hex t'
    rw [hμ] at h
    obtain ⟨-, -, -, hs⟩ := h
    simp [hs]
  | discard p' q' m' =>
    rw [hμ] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    have h := hex t'
    rw [hμ] at h
    exact delivered_subset (hex t') _ h.2.2.1
  | _ => rw [hμ] at hr; exact hr.elim

-- A process that completes the R-broadcast of `m`, or completes the relay of a message it does
-- not send, has sent `m` to every process.
private theorem mem_chan_of_broadcast (hex : lts.OmegaExecution ss μs) {p : P} {t : ℕ}
    {m : Message P D} (hμ : μs t = .broadcast p m none) (r : P) :
    m ∈ (ss (t + 1)).chan p r := by
  have h := hex t
  rw [hμ] at h
  obtain ⟨-, -, -, hs⟩ := h
  rw [hs]
  exact mem_send_none _ _ _ _

private theorem mem_chan_of_deliver (hex : lts.OmegaExecution ss μs) {p q : P} {t : ℕ}
    {m : Message P D} (hμ : μs t = .deliver p q m none) (hne : m.sender ≠ p) (r : P) :
    m ∈ (ss (t + 1)).chan p r := by
  have h := hex t
  rw [hμ] at h
  obtain ⟨-, -, -, hs⟩ := h
  rw [hs]
  simp only [hne, ↓reduceIte]
  exact mem_send_none _ _ _ _

end Diffusion

open Diffusion in
/-- **Diffusion implements reliable broadcast.** Consider processes `P`, which may crash, and
messages that carry their sender, a sequence number and a payload of type `D`. A state gives the
set of crashed processes; for each process, the sequence number of its next message and the set
of messages it has received; and for each ordered pair of processes `q, p`, the channel from `q`
to `p`, the multiset of copies of messages that `q` has sent to `p` and `p` has not yet received.
In the initial state no process has crashed, every sequence number is `0`, and every set and
channel is empty. A process that has not crashed takes the following steps of the diffusion
algorithm.

* R-broadcast: it R-broadcasts a message `m` whose sender it is, with its next sequence number,
  which it then increments, and sends a copy of `m` to every process, itself included.
* Receipt: it takes a copy of a message `m` from a channel to it. If it has not received `m`
  before, it sends a copy of `m` to every process unless it is the sender of `m`, and then adds
  `m` to the messages it has received and R-delivers `m`. Otherwise it discards the copy.
* Crash: it crashes, and takes no step afterwards. It may also crash during an R-broadcast of
  `m`, which is still an R-broadcast of `m`, or during the receipt of a message `m` it has not
  received before, which then does not R-deliver `m`. It has then sent copies of `m` only to the
  processes of some finite set.

A step may also leave the state unchanged. Take an execution: states `s 0, s 1, …`, with `s 0`
initial, and steps `μ 0, μ 1, …`, where `μ t` takes `s t` to `s (t + 1)`; its event at time `t`
is the R-broadcast or R-deliver of `μ t`, if any. A process is correct if it never crashes.
Suppose that channels to correct processes are reliable: whenever a copy of `m` is in the
channel from `q` to a correct process `p` in `s t`, some step `μ t'` with `t' ≥ t` is a receipt
by `p` of a copy of `m` from that channel. Then the execution, with its correct processes and
its events, satisfies reliable broadcast (`IsReliableBroadcast`): validity, agreement and
uniform integrity. Neither the number of processes nor the number of crashes is bounded. -/
theorem diffusion_isReliableBroadcast [DecidableEq P] [DecidableEq D]
    {ss : ωSequence (State P D)} {μs : ωSequence (Step P D)} (h0 : ss 0 = init)
    (hex : lts.OmegaExecution ss μs) (hfair : ReliableDelivery ss μs) :
    IsReliableBroadcast Message.sender (correct ss) fun t => (μs t).event := by
  -- Every message in a delivered set has been R-delivered.
  have hdel : ∀ p m T, m ∈ (ss T).delivered p → ∃ t, (μs t).event = some (.deliver p m) := by
    intro p m T hm
    obtain ⟨t, -, -, q, hμ⟩ :=
      exists_deliver_of_mem hex (t₁ := 0) (by simp [h0, init]) hm
    exact ⟨t, event_eq_deliver.2 ⟨q, hμ⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Validity.
    intro p hp m t he
    obtain ⟨cut, hμ⟩ := event_eq_broadcast.1 he
    have hcut := cut_eq_none_of_broadcast hex hp hμ
    subst hcut
    have h := hex t
    rw [hμ] at h
    obtain ⟨-, hs, hq, -⟩ := h
    obtain ⟨T, hT⟩ := exists_mem_delivered hex hfair hp (mem_chan_of_broadcast hex hμ p)
    have hnot : m ∉ (ss t).delivered p :=
      (not_mem_of_nextSeq_le h0 hex (by rw [hs, hq])).2 p
    obtain ⟨t', ht, -, q, hμ'⟩ := exists_deliver_of_mem hex hnot hT
    exact ⟨t', ht, event_eq_deliver.2 ⟨q, hμ'⟩⟩
  · -- Agreement.
    intro p hp m t he r hr
    obtain ⟨q, hμ⟩ := event_eq_deliver.1 he
    -- Some step has sent `m` to every process.
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, ∀ r, m ∈ (ss t₀).chan p r := by
      by_cases hs : m.sender = p
      · have h := hex t
        rw [hμ] at h
        obtain ⟨t', -, he'⟩ := exists_broadcast_of_mem_chan h0 hex h.2.1
        rw [hs] at he'
        obtain ⟨cut, hμ'⟩ := event_eq_broadcast.1 he'
        have hcut := cut_eq_none_of_broadcast hex hp hμ'
        subst hcut
        exact ⟨t' + 1, mem_chan_of_broadcast hex hμ'⟩
      · exact ⟨t + 1, mem_chan_of_deliver hex hμ hs⟩
    obtain ⟨T, hT⟩ := exists_mem_delivered hex hfair hr (ht₀ r)
    exact hdel r m T hT
  · -- Uniform integrity.
    intro p m t he
    obtain ⟨q, hμ⟩ := event_eq_deliver.1 he
    have h := hex t
    rw [hμ] at h
    obtain ⟨-, hc, hnot, hs⟩ := h
    have hin : m ∈ (ss (t + 1)).delivered p := by simp [hs]
    refine ⟨fun t' he' => ?_, exists_broadcast_of_mem_chan h0 hex hc⟩
    obtain ⟨q', hμ'⟩ := event_eq_deliver.1 he'
    have h' := hex t'
    rw [hμ'] at h'
    obtain ⟨-, -, hnot', hs'⟩ := h'
    have hin' : m ∈ (ss (t' + 1)).delivered p := by simp [hs']
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hnot (delivered_mono hex hlt p hin')
    · exact hnot' (delivered_mono hex hlt p hin)

end Cslib.Distributed.ReliableBroadcast
