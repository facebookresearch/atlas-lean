/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Paxos.Voting
public import CSLibExt.Computability.Distributed.ReliableBroadcast

/-!
# Rotating-coordinator consensus: the protocol

A safety abstraction of the asynchronous steps in Chandra and Toueg, *Unreliable failure detectors
for reliable distributed systems*, JACM 43(2), 1996, §2.5 and §6.2, Figure 6. A tick orders events;
no process reads time or advances because another process advanced. A round's coordinator has
zero-based index `r % n`, i.e. process number `(r mod n) + 1` in the paper.

The event history represents both registers and unordered channels. A sent ordinary message
is pending until its one reception. `receive` must match the entire addressed message; delayed
and stale arrivals are allowed. Reports are frozen at send time. Sending a suggestion to all
is split into individual sends of the single selected value: a coordinator may crash partway.
Reception into an inbox is separate from acting on the inbox, so messages may arrive early.
For each ordinary message the pending-copy count is its send indicator minus its reception
indicator: program order prevents repeat reports and replies, and the send guard prevents repeat
fanout to a recipient. Thus membership in an unordered channel is exactly “sent, not received”.
The inbox need only retain arrivals tagged for the current or future local round. Keeping stale
arrivals in the log cannot enable a later round. A partial iteration can stop between actions;
`advance` tests the while guard, so deciding mid-iteration does not erase an outstanding send.
A live process may poll (`wait p`) even at an enabled instruction. No finite prefix requires
fair scheduling, delivery by a deadline or progress to the next instruction.

The phase program counter is represented by the last numbered instruction of each process.
Starting the next round requires the previous round's final local instruction. A process can
send a NACK only on suspicion and only before receiving the matching suggestion. Only adoption
writes the timestamp; the printed Phase 2 also writes the coordinator's outgoing value into
its estimate register, even before the self-addressed message is received. These are separate
writes. A round finishes with a decision request only on a strict majority of ACKs, not merely
of replies. Only decision requests use reliable broadcast. Its semantic events are the actual
Phase 4 broadcasts and deliveries, not ordinary fanout or application decisions.

One consensus instance is modelled. A process invokes `propose` at most once in a program prefix:
its invocation has a fixed positive slot, and slots must strictly increase. Figure 6 sets the
local state to undecided inside `propose` and does not specify its value before invocation. Here
the handler is initially unarmed. An earlier upcall is an R-delivery but does not decide or get
replayed. The first upcall after the local proposal decides; later upcalls are still deliveries
but do not decide again. No global ordering of proposals before upcalls is required.
-/

@[expose] public section

namespace Cslib.Distributed.RotatingCoordinator

variable {n : ℕ} {V : Type*}

/-- Process identifiers are zero based; `n + 1` is the nonzero population size. -/
abbrev Proc (n : ℕ) := Fin (n + 1)

/-- The coordinator of positive round `r`, with the paper's process numbers shifted down by one. -/
def coord (n r : ℕ) : Proc n := ⟨r % (n + 1), Nat.mod_lt _ (by omega)⟩

/-- Ordinary, addressed, round-tagged messages. Reports and replies go to the coordinator;
`suggest` goes from the coordinator to the named recipient. -/
inductive Wire (n : ℕ) (V : Type*) where
  | report (from_ : Proc n) (round stamp : ℕ) (value : V)
  | suggest (to_ : Proc n) (round : ℕ) (value : V)
  | reply (from_ : Proc n) (round : ℕ) (ack : Bool)
  deriving DecidableEq

/-- One interleaved program, channel or broadcast action. `finish r none` ends a failed round;
`finish r (some v)` R-broadcasts. `deliver` is an upcall, not necessarily a decision. -/
inductive Event (n : ℕ) (V : Type*) where
  | idle
  | wait (p : Proc n)
  | propose (p : Proc n) (v : V)
  | advance (p : Proc n) (r : ℕ)
  | report (p : Proc n) (r s : ℕ) (v : V)
  | choose (r s : ℕ) (v : V)
  | send (to_ : Proc n) (r : ℕ) (v : V)
  | ack (p : Proc n) (r : ℕ) (v : V)
  | nack (p : Proc n) (r : ℕ)
  | finish (r : ℕ) (out : Option V)
  | receive (m : Wire n V)
  | deliver (p : Proc n) (r : ℕ) (v : V)
  deriving DecidableEq

namespace Event

-- The process taking this step, including receipt of an ordinary or R-broadcast message.
def actor : Event n V → Option (Proc n)
  | .idle => none
  | .wait p | .propose p _ | .advance p _ | .report p ..
  | .ack p .. | .nack p _ | .deliver p .. => some p
  | .choose r .. | .send _ r _ | .finish r _ => some (coord n r)
  | .receive (.report _ r ..) | .receive (.reply _ r _) => some (coord n r)
  | .receive (.suggest p ..) => some p

-- Numbered program instructions; zero is not an instruction. The five round slots increase
-- even when different processes' rounds overlap in external time.
def slot (e : Event n V) (p : Proc n) : ℕ :=
  if e.actor = some p then match e with
    | .propose .. => 1
    | .advance _ r => 5 * r + 1
    | .report _ r .. => 5 * r + 2
    | .choose r .. => 5 * r + 3
    | .ack _ r _ | .nack _ r => 5 * r + 4
    | .finish r _ => 5 * r + 5
    | _ => 0
  else 0

-- A write to the value register, tagged by its local round (zero at actual input).
def writeAt (p : Proc n) : Event n V → Option (ℕ × V)
  | .propose q v => if p = q then some (0, v) else none
  | .choose r _ v => if p = coord n r then some (r, v) else none
  | .ack q r v => if p = q then some (r, v) else none
  | _ => none

-- The timestamp changes only upon receiving and adopting the round suggestion.
def adoption (p : Proc n) : Event n V → ℕ
  | .ack q r _ => if p = q then r else 0
  | _ => 0

-- The ordinary message emitted by this action, if any.
def sent : Event n V → Option (Wire n V)
  | .report p r s v => some (.report p r s v)
  | .send p r v => some (.suggest p r v)
  | .ack p r _ => some (.reply p r true)
  | .nack p r => some (.reply p r false)
  | _ => none

-- The destination and round of an individual suggestion send, independent of its payload.
def route : Event n V → Option (Proc n × ℕ)
  | .send p r _ => some (p, r)
  | _ => none

-- Phase 2 inspects only delivered reports of this sender for this particular round.
def incoming (r : ℕ) (p : Proc n) : Event n V → Option (ℕ × V)
  | .receive (.report q k s v) => if r = k ∧ p = q then some (s, v) else none
  | _ => none

-- The single value selected by the coordinator, before transmission to any recipients.
def selection (r : ℕ) : Event n V → Option V
  | .choose k _ v => if k = r then some v else none
  | _ => none

-- Receipt of the matching suggestion in the local inbox.
def suggested (p : Proc n) (r : ℕ) : Event n V → Option V
  | .receive (.suggest q k v) => if p = q ∧ r = k then some v else none
  | _ => none

-- Only `propose` invokes the procedure, including on raw streams with illegal round numbers.
def invoker : Event n V → Option (Proc n)
  | .propose p _ => some p
  | _ => none

-- Identify an upcall to this recipient; OpenGuard separately tests whether it was armed.
def upcall (p : Proc n) : Event n V → Option V
  | .deliver q _ v => if p = q then some v else none
  | _ => none

/-- Reliable-broadcast projection. Round and value identify a decision request; its sender is
the rotating coordinator. Every upcall is an R-delivery, including one before local invocation
and one after the process has already decided. -/
def rb : Event n V → Option (ReliableBroadcast.Event (Proc n) (ℕ × V))
  | .finish r (some v) => some (.broadcast (coord n r) (r, v))
  | .deliver p r v => some (.deliver p (r, v))
  | _ => none

end Event

variable (ev : ℕ → Event n V)

-- Read the last matching write before `t`, with no preloaded value.
def latest {A : Type*} (read : Event n V → Option A) : ℕ → Option A
  | 0 => none
  | t + 1 => (read (ev t)).orElse fun _ => latest read t

/-- The maximum of zero and the round numbers of all `ack p` events strictly before `t`.
This is a prefix maximum even on an arbitrary stream. On a program prefix, ACKs by `p` are
ordered adoptions, so it equals the most recent adoption round, or zero if there was none. -/
def stamp (p : Proc n) : ℕ → ℕ
  | 0 => 0
  | t + 1 => max (stamp p t) ((ev t).adoption p)

-- A finite history test; the current event is deliberately excluded.
abbrev Seen (t : ℕ) (check : Event n V → Prop) := ∃ i : Fin t, check (ev i)

-- The decision handler is armed by the actual proposal. Upcalls before initialisation do
-- not consume the guard; after the first armed upcall it never opens again.
abbrev OpenGuard (p : Proc n) (t : ℕ) :=
  Seen ev t (fun e => e.invoker = some p) ∧ ∀ i : Fin t,
    (Event.upcall p (ev i)).isSome → ¬ Seen ev i (fun e => e.invoker = some p)

-- The set of distinct report senders whose messages have reached this coordinator.
def reporters (t r : ℕ) : Finset (Proc n) :=
  Finset.univ.filter fun p => (latest ev (Event.incoming r p) t).isSome

variable [DecidableEq V]

-- Senders of received ACKs, or of either kind of reply.
def replies (t r : ℕ) (acksOnly : Bool) : Finset (Proc n) :=
  Finset.univ.filter fun p => Seen ev t fun e =>
    e = .receive (.reply p r true) ∨ (acksOnly = false ∧ e = .receive (.reply p r false))

-- The last iteration is over only when the local last instruction is over: coordinator Phase 4
-- versus noncoordinator Phase 3. Use slots so the test does not need a default value of `V`.
abbrev Done (t : ℕ) (p : Proc n) (r : ℕ) :=
  Seen ev t fun e => e.slot p = (if p = coord n r then 5 * r + 5 else 5 * r + 4)

-- Preconditions common to both Phase 3 branches; the coordinator completes its own fanout first.
abbrev ReadyToReply (t : ℕ) (p : Proc n) (r : ℕ) :=
  Seen ev t (fun e => e.slot p = 5 * r + 2) ∧
    (p = coord n r → ∀ q : Proc n, Seen ev t fun e => e.route = some (q, r))

/-- Local instruction and channel guards. A reception consumes a previously sent, not already
received message. `H` is sampled only at an actual NACK. Delivery by the RB service is a separate
input whose causal integrity is imposed by `LegalPrefix` or by the article's broadcast primitive.
`wait p` has no instruction-readiness test; the separate actor guard requires `p` to be alive. -/
def Guard (H : FailureDetector.History (Proc n)) (t : ℕ) : Event n V → Prop
  | .idle | .wait .. | .propose .. | .deliver .. => True
  | .advance p r =>
    0 < r ∧ OpenGuard ev p t ∧
    (r = 1 ∨ Done ev t p (r - 1))
  | .report p r s v =>
    0 < r ∧ Seen ev t (fun e => e = .advance p r) ∧
    (latest ev (Event.writeAt p) t).map Prod.snd = some v ∧ s = stamp ev p t
  | .choose r s v =>
    0 < r ∧ Seen ev t (fun e => e.slot (coord n r) = 5 * r + 2) ∧
    (Paxos.QuorumSystem.majority (Proc n)).IsQuorum (reporters ev t r) ∧
    (∃ p : Proc n, latest ev (Event.incoming r p) t = some (s, v)) ∧
    ∀ p : Proc n, ((latest ev (Event.incoming r p) t).map Prod.fst).getD 0 ≤ s
  | .send p r v => latest ev (Event.selection r) t = some v ∧
    ¬ Seen ev t (fun e => e = .send p r v) ∧ ∀ i : Fin t, (ev i).slot (coord n r) < 5 * r + 4
  | .ack p r v => ReadyToReply ev t p r ∧ latest ev (Event.suggested p r) t = some v
  | .nack p r => ReadyToReply ev t p r ∧
    latest ev (Event.suggested p r) t = none ∧ coord n r ∈ H p t
  | .finish r out =>
    Seen ev t (fun e => e.slot (coord n r) = 5 * r + 4) ∧
    (Paxos.QuorumSystem.majority (Proc n)).IsQuorum (replies ev t r false) ∧
    (if (replies ev t r true).card * 2 > n + 1 then
      out.isSome ∧ latest ev (Event.selection r) t = out else out = none)
  | .receive m => Seen ev t (fun e => e.sent = some m) ∧ ¬ Seen ev t (fun e => e = .receive m)

-- All guards for appending one event. Only positions strictly before `t` are inspected.
def Enabled (F : FailureDetector.FailurePattern (Proc n))
    (H : FailureDetector.History (Proc n)) (t : ℕ) (e : Event n V) : Prop :=
  (∀ p, e.actor = some p → p ∉ F.crashedBy t) ∧
    (∀ p, e.slot p ≠ 0 → ∀ i : Fin t, (ev i).slot p < e.slot p) ∧ Guard ev H t e

/-- A finite prefix of program and channel steps, before tick `T`. The indexed crash set is
external: no action can be taken by its actor after it crashes. Program slots strictly advance
locally; unnumbered inbox, fanout and delivery actions need not advance the program counter. -/
def ProgramPrefix (F : FailureDetector.FailurePattern (Proc n))
    (H : FailureDetector.History (Proc n)) (T : ℕ) : Prop :=
  ∀ t : Fin T, Enabled ev F H t (ev t)

/-- A program prefix with the no-creation part of reliable broadcast: every delivered request
was broadcast in a strictly earlier Phase 4. Progress and duplicate suppression are unnecessary
for the prefix safety theorem. -/
def LegalPrefix (F : FailureDetector.FailurePattern (Proc n))
    (H : FailureDetector.History (Proc n)) (T : ℕ) : Prop :=
  ProgramPrefix ev F H T ∧ ∀ (t : Fin T) p r v, ev t = .deliver p r v →
    Seen ev t fun e => e = .finish r (some v)

/-- Process `p` decides `v` at tick `t` when a `deliver p r v` occurs after an actual local
`propose` and no earlier delivery to `p` occurred after a local proposal. No correctness premise
restricts `p`. Figure 6 initialises the handler inside `propose`; it does not specify behaviour
before invocation. Here an early R-delivery is ignored locally and is not replayed. Later
R-deliveries after a first decision are ignored for decision only. Program prefixes model one
invocation at most per process; even on a raw stream a second proposal cannot re-arm the guard. -/
def Decides (p : Proc n) (t : ℕ) (v : V) : Prop :=
  (∃ r, ev t = .deliver p r v) ∧ OpenGuard ev p t

end Cslib.Distributed.RotatingCoordinator
