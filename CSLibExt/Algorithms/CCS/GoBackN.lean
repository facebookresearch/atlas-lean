/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Go-back-N
-/
module

public import CSLibExt.Algorithms.CCS.FiniteState

/-!
# Go-back-N with window 2

The go-back-N sliding-window protocol (Tanenbaum, *Computer Networks*,
"Protocol 5: go-back-n"; Kurose and Ross, *Computer Networking*, the go-back-N
section), with window size `2` and sequence numbers modulo `3`, as a finite-state
system in the recursive CCS of `CSLibExt/Languages/CCS/`, checked with the
certificates of `FiniteState.lean`.

* The sender keeps the base `b` of its window, the number `c ≤ 2` of
  outstanding (unacknowledged) messages, and the offset `o ≤ c` of the next frame
  to transmit. It accepts a message (`acc`) while `c < 2`, transmits frames
  `b + o` in order, and on a silent timeout goes back to the base and
  retransmits all outstanding frames. A cumulative acknowledgement `k`
  (the receiver expects `k` next) inside the window slides it to `k`; any other
  acknowledgement is ignored.
* The data channel holds at most one frame and may silently lose it.
* The receiver, expecting `e`, delivers (`del`) the frame `e` and acknowledges
  `e + 1`; any other frame is discarded and `e` is acknowledged again.
* Acknowledgements reach the sender reliably: the receiver's acknowledgement
  synchronizes directly with the sender. For this receiver, which delivers a
  frame before acknowledging it and takes no other frame in between, that is
  needed: `lossyGoBackN_not_weaklyBisimilar_buffer` shows that with a lossy
  one-place acknowledgement channel the protocol is not weakly bisimilar to the
  two-place buffer. After the acknowledgement of the first message is lost, the
  window stays full while the receiver holds the second message, so the
  protocol refuses a new message that the buffer, holding one, accepts. A
  receiver that acknowledges retransmitted frames while it waits to deliver is
  not covered.
* Messages carry no payload, so the theorem is about control flow.

The main theorem `goBackN_weaklyBisimilar_buffer`: the protocol is weakly
bisimilar, indeed observation congruent (`goBackN_observationCongruent_buffer`),
to a two-place buffer, which accepts up to two messages ahead of their delivery.
The proof is a 147-pair certificate (every reachable configuration with the
buffer occupancy it simulates), checked with `decide +kernel`.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.GoBackN

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

/-- Channel names; sequence numbers are `0`, `1`, `2`. -/
inductive Name
  /-- Accept a message from the user. -/
  | acc
  /-- Deliver a message to the user. -/
  | del
  /-- Sender to data channel, a frame with this sequence number. -/
  | send (k : ℕ)
  /-- Data channel to receiver. -/
  | recv (k : ℕ)
  /-- Receiver to sender: cumulative acknowledgement, the next expected frame. -/
  | ack (k : ℕ)
  /-- Receiver to the acknowledgement channel, in the lossy variant. -/
  | reply (k : ℕ)
  deriving DecidableEq

/-- Sender state: window base, number of outstanding messages, offset of the
next frame to transmit. -/
structure Sender where
  /-- The sequence number of the oldest unacknowledged frame. -/
  base : ℕ
  /-- The number of outstanding (accepted, unacknowledged) messages. -/
  out : ℕ
  /-- The offset from `base` of the next frame to transmit. -/
  next : ℕ
  deriving DecidableEq

/-- Receiver states. -/
inductive Receiver
  /-- Expecting this sequence number. -/
  | expect (e : ℕ)
  /-- Received the expected frame `e`; about to deliver it. -/
  | deliver (e : ℕ)
  /-- About to acknowledge: the next expected sequence number. -/
  | reply (k : ℕ)
  deriving DecidableEq

/-- The window slides on an acknowledgement `k` that acknowledges `d ≥ 1`
outstanding frames; other acknowledgements are ignored. -/
def ackUpdate (s : Sender) (k : ℕ) : Sender :=
  if 1 ≤ (k + 3 - s.base) % 3 ∧ (k + 3 - s.base) % 3 ≤ s.out then
    ⟨k, s.out - (k + 3 - s.base) % 3, s.next - (k + 3 - s.base) % 3⟩
  else s

/-- Sender transitions. -/
def senderSteps (s : Sender) : List (Label Name × Sender) :=
  (if s.out < 2 then [(.input .acc, ⟨s.base, s.out + 1, s.next⟩)] else []) ++
  (if s.next < s.out then
    [(.output (.send ((s.base + s.next) % 3)), ⟨s.base, s.out, s.next + 1⟩)] else []) ++
  (if 0 < s.out then [(.tau, ⟨s.base, s.out, 0⟩)] else []) ++
  [0, 1, 2].map fun k => (.input (.ack k), ackUpdate s k)

/-- Lossy one-place data channel. -/
def dataSteps : Option ℕ → List (Label Name × Option ℕ)
  | none => [0, 1, 2].map fun k => (.input (.send k), some k)
  | some k => [(.output (.recv k), none), (.tau, none)]

/-- Receiver transitions. -/
def receiverSteps : Receiver → List (Label Name × Receiver)
  | .expect e => [0, 1, 2].map fun k =>
      (.input (.recv k), if k = e then .deliver e else .reply e)
  | .deliver e => [(.output .del, .reply ((e + 1) % 3))]
  | .reply k => [(.output (.ack k), .expect k)]

/-- A two-place buffer, by occupancy. -/
def bufferSteps (n : ℕ) : List (Label Name × ℕ) :=
  (if n < 2 then [(.input .acc, n + 1)] else []) ++
  (if 0 < n then [(.output .del, n - 1)] else [])

/-- Lossy one-place acknowledgement channel, for the lossy variant. -/
def ackChannelSteps : Option ℕ → List (Label Name × Option ℕ)
  | none => [0, 1, 2].map fun k => (.input (.reply k), some k)
  | some k => [(.output (.ack k), none), (.tau, none)]

/-- The receiver of the lossy variant: acknowledgements go to the channel. -/
def lossyReceiverSteps : Receiver → List (Label Name × Receiver)
  | .reply k => [(.output (.reply k), .expect k)]
  | r => receiverSteps r

/-- Process constants: one per state of each agent. -/
inductive Agent
  | sender (s : Sender)
  | data (k : Option ℕ)
  | receiver (r : Receiver)
  | buffer (n : ℕ)
  | ackChannel (k : Option ℕ)
  | lossyReceiver (r : Receiver)

/-- The recursive specification: each constant is the choice of its listed
transitions. -/
def spec : Specification Name Agent
  | .sender s => sumOf ((senderSteps s).map fun y => (y.1, .constant (.sender y.2)))
  | .data k => sumOf ((dataSteps k).map fun y => (y.1, .constant (.data y.2)))
  | .receiver r => sumOf ((receiverSteps r).map fun y => (y.1, .constant (.receiver y.2)))
  | .buffer n => sumOf ((bufferSteps n).map fun y => (y.1, .constant (.buffer y.2)))
  | .ackChannel k => sumOf ((ackChannelSteps k).map fun y => (y.1, .constant (.ackChannel y.2)))
  | .lossyReceiver r =>
      sumOf ((lossyReceiverSteps r).map fun y => (y.1, .constant (.lossyReceiver y.2)))

/-- The labelled transition system of the specification. -/
abbrev lts : LTS (Process Name Agent) (Label Name) := Process.lts spec

/-- The internal channels, all restricted. -/
def internal : List Name :=
  [.send 0, .send 1, .send 2, .recv 0, .recv 1, .recv 2, .ack 0, .ack 1, .ack 2]

/-- Protocol configurations: sender, data channel, receiver. -/
abbrev Config := (Sender × Option ℕ) × Receiver

/-- The protocol process in a configuration. -/
def system (c : Config) : Process Name Agent :=
  .restriction internal
    (.parallel (.parallel (.constant (.sender c.1.1)) (.constant (.data c.1.2)))
      (.constant (.receiver c.2)))

/-- The configuration-level transitions of the protocol. -/
def configSteps : Config → List (Label Name × Config) :=
  restrictSteps internal (parSteps (parSteps senderSteps dataSteps) receiverSteps)

theorem realizes_system : Realizes spec system configSteps :=
  (((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.receiver receiverSteps fun _ => rfl)).restriction internal

/-- The buffer process with the given occupancy. -/
def buffer (n : ℕ) : Process Name Agent := .constant (.buffer n)

theorem realizes_buffer : Realizes spec buffer bufferSteps :=
  Realizes.constant Agent.buffer bufferSteps fun _ => rfl

/-- The initial configuration: empty window based at `0`, empty channel, the
receiver expecting `0`. -/
def initial : Config := ((⟨0, 0, 0⟩, none), .expect 0)

/-- The go-back-N protocol. -/
def goBackN : Process Name Agent := system initial

/-- The empty two-place buffer. -/
def buf : Process Name Agent := buffer 0

/-- The weak-bisimulation certificate: every reachable configuration with the
number of accepted but undelivered messages, listed so that every pair can
reach the visible actions of its buffer state through pairs listed earlier. -/
def certificate : List (Config × ℕ) := [
  (((⟨0, 2, 1⟩, none), .deliver 0), 2), (((⟨1, 2, 2⟩, some 2), .deliver 1), 2),
  (((⟨1, 2, 0⟩, none), .deliver 1), 2), (((⟨2, 2, 0⟩, some 0), .deliver 2), 2),
  (((⟨2, 2, 1⟩, some 2), .deliver 2), 2), (((⟨0, 2, 0⟩, none), .deliver 0), 2),
  (((⟨2, 2, 2⟩, none), .deliver 2), 2), (((⟨2, 2, 0⟩, some 2), .deliver 2), 2),
  (((⟨1, 2, 1⟩, some 1), .deliver 1), 2), (((⟨1, 2, 1⟩, none), .deliver 1), 2),
  (((⟨0, 2, 2⟩, some 1), .deliver 0), 2), (((⟨1, 2, 2⟩, none), .deliver 1), 2),
  (((⟨1, 0, 0⟩, none), .reply 1), 0), (((⟨1, 2, 0⟩, some 1), .expect 1), 2),
  (((⟨2, 2, 1⟩, none), .deliver 2), 2), (((⟨0, 2, 0⟩, some 0), .deliver 0), 2),
  (((⟨1, 1, 0⟩, none), .deliver 1), 1), (((⟨0, 1, 0⟩, none), .reply 1), 0),
  (((⟨2, 1, 0⟩, none), .reply 0), 0), (((⟨0, 1, 1⟩, some 0), .deliver 0), 1),
  (((⟨1, 1, 1⟩, some 1), .reply 2), 0), (((⟨0, 1, 0⟩, some 0), .deliver 0), 1),
  (((⟨1, 1, 1⟩, none), .reply 2), 0), (((⟨2, 1, 1⟩, some 2), .deliver 2), 1),
  (((⟨2, 0, 0⟩, none), .expect 2), 0), (((⟨2, 2, 1⟩, some 2), .expect 2), 2),
  (((⟨2, 1, 0⟩, some 2), .deliver 2), 1), (((⟨0, 0, 0⟩, none), .reply 0), 0),
  (((⟨0, 0, 0⟩, some 2), .expect 0), 0), (((⟨1, 2, 0⟩, some 1), .reply 1), 2),
  (((⟨2, 2, 0⟩, none), .deliver 2), 2), (((⟨1, 1, 0⟩, some 1), .deliver 1), 1),
  (((⟨0, 1, 1⟩, none), .deliver 0), 1), (((⟨2, 1, 0⟩, none), .deliver 2), 1),
  (((⟨1, 2, 0⟩, some 1), .deliver 1), 2), (((⟨0, 1, 0⟩, none), .deliver 0), 1),
  (((⟨0, 2, 0⟩, some 0), .expect 0), 2), (((⟨0, 0, 0⟩, none), .expect 0), 0),
  (((⟨0, 2, 0⟩, some 1), .deliver 0), 2), (((⟨0, 2, 1⟩, some 0), .deliver 0), 2),
  (((⟨2, 1, 1⟩, none), .reply 0), 0), (((⟨1, 1, 1⟩, none), .deliver 1), 1),
  (((⟨0, 1, 1⟩, some 0), .expect 0), 1), (((⟨2, 2, 0⟩, some 2), .expect 2), 2),
  (((⟨2, 0, 0⟩, none), .reply 2), 0), (((⟨2, 2, 1⟩, some 2), .reply 2), 2),
  (((⟨1, 1, 0⟩, none), .reply 2), 0), (((⟨0, 1, 0⟩, some 0), .expect 0), 1),
  (((⟨1, 0, 0⟩, some 0), .expect 1), 0), (((⟨2, 2, 0⟩, some 2), .reply 2), 2),
  (((⟨2, 1, 0⟩, some 2), .expect 2), 1), (((⟨1, 2, 1⟩, some 1), .expect 1), 2),
  (((⟨2, 2, 2⟩, some 0), .reply 0), 1), (((⟨2, 1, 1⟩, none), .deliver 2), 1),
  (((⟨2, 2, 0⟩, none), .expect 2), 2), (((⟨0, 1, 1⟩, some 0), .reply 1), 0),
  (((⟨0, 1, 0⟩, some 0), .reply 1), 0), (((⟨1, 0, 0⟩, none), .expect 1), 0),
  (((⟨2, 2, 0⟩, some 0), .reply 0), 1), (((⟨2, 0, 0⟩, some 1), .expect 2), 0),
  (((⟨0, 2, 1⟩, some 0), .expect 0), 2), (((⟨1, 1, 1⟩, some 1), .deliver 1), 1),
  (((⟨0, 2, 2⟩, none), .deliver 0), 2), (((⟨1, 2, 0⟩, some 2), .deliver 1), 2),
  (((⟨2, 1, 1⟩, some 2), .reply 0), 0), (((⟨1, 1, 0⟩, some 1), .reply 2), 0),
  (((⟨2, 1, 0⟩, some 2), .reply 0), 0), (((⟨2, 2, 2⟩, some 0), .deliver 2), 2),
  (((⟨0, 1, 1⟩, none), .reply 1), 0), (((⟨2, 2, 1⟩, none), .reply 0), 1),
  (((⟨2, 2, 0⟩, some 1), .expect 2), 2), (((⟨2, 1, 0⟩, some 2), .reply 2), 1),
  (((⟨1, 2, 1⟩, some 1), .reply 1), 2), (((⟨2, 2, 0⟩, none), .reply 2), 2),
  (((⟨0, 1, 0⟩, none), .expect 0), 1), (((⟨1, 1, 0⟩, some 1), .expect 1), 1),
  (((⟨2, 2, 0⟩, some 0), .expect 2), 2), (((⟨0, 2, 0⟩, some 0), .reply 0), 2),
  (((⟨1, 2, 0⟩, some 2), .reply 2), 1), (((⟨2, 2, 2⟩, none), .expect 2), 2),
  (((⟨1, 1, 0⟩, some 1), .reply 1), 1), (((⟨1, 2, 2⟩, some 2), .reply 2), 1),
  (((⟨2, 2, 2⟩, some 0), .expect 2), 2), (((⟨0, 1, 1⟩, some 0), .reply 0), 1),
  (((⟨1, 1, 1⟩, some 1), .expect 1), 1), (((⟨0, 1, 0⟩, some 0), .reply 0), 1),
  (((⟨1, 2, 1⟩, none), .reply 2), 1), (((⟨0, 2, 2⟩, some 1), .reply 1), 1),
  (((⟨2, 2, 0⟩, some 0), .reply 2), 2), (((⟨0, 2, 0⟩, none), .expect 0), 2),
  (((⟨1, 2, 0⟩, none), .expect 1), 2), (((⟨2, 2, 2⟩, none), .reply 2), 2),
  (((⟨2, 1, 1⟩, some 2), .expect 2), 1), (((⟨0, 1, 0⟩, some 2), .expect 0), 1),
  (((⟨0, 2, 1⟩, some 0), .reply 0), 2), (((⟨2, 2, 1⟩, none), .expect 2), 2),
  (((⟨1, 2, 2⟩, none), .expect 1), 2), (((⟨2, 2, 1⟩, none), .reply 2), 2),
  (((⟨1, 2, 0⟩, some 0), .expect 1), 2), (((⟨0, 1, 1⟩, none), .expect 0), 1),
  (((⟨2, 2, 2⟩, some 0), .reply 2), 2), (((⟨2, 1, 0⟩, none), .expect 2), 1),
  (((⟨1, 1, 1⟩, some 1), .reply 1), 1), (((⟨1, 1, 0⟩, none), .expect 1), 1),
  (((⟨0, 2, 0⟩, some 1), .expect 0), 2), (((⟨2, 2, 1⟩, some 2), .reply 0), 1),
  (((⟨2, 2, 0⟩, some 2), .reply 0), 1), (((⟨1, 2, 0⟩, none), .reply 1), 2),
  (((⟨0, 1, 0⟩, none), .reply 0), 1), (((⟨2, 1, 1⟩, some 2), .reply 2), 1),
  (((⟨2, 2, 0⟩, none), .reply 0), 1), (((⟨0, 2, 0⟩, some 1), .reply 1), 1),
  (((⟨1, 2, 2⟩, none), .reply 1), 2), (((⟨2, 1, 0⟩, none), .reply 2), 1),
  (((⟨1, 1, 0⟩, none), .reply 1), 1), (((⟨0, 2, 2⟩, none), .expect 0), 2),
  (((⟨0, 2, 0⟩, some 2), .expect 0), 2), (((⟨1, 1, 1⟩, none), .expect 1), 1),
  (((⟨2, 1, 0⟩, some 1), .expect 2), 1), (((⟨0, 2, 1⟩, none), .expect 0), 2),
  (((⟨2, 1, 1⟩, none), .expect 2), 1), (((⟨0, 2, 2⟩, none), .reply 1), 1),
  (((⟨2, 1, 1⟩, none), .reply 2), 1), (((⟨0, 2, 2⟩, some 1), .expect 0), 2),
  (((⟨0, 2, 1⟩, none), .reply 1), 1), (((⟨1, 2, 1⟩, none), .expect 1), 2),
  (((⟨0, 2, 0⟩, none), .reply 0), 2), (((⟨1, 2, 1⟩, some 1), .reply 2), 1),
  (((⟨0, 2, 2⟩, some 1), .reply 0), 2), (((⟨1, 2, 0⟩, some 2), .expect 1), 2),
  (((⟨1, 1, 1⟩, none), .reply 1), 1), (((⟨1, 2, 2⟩, none), .reply 2), 1),
  (((⟨2, 2, 2⟩, none), .reply 0), 1), (((⟨1, 2, 2⟩, some 2), .expect 1), 2),
  (((⟨1, 2, 2⟩, some 2), .reply 1), 2), (((⟨0, 1, 1⟩, none), .reply 0), 1),
  (((⟨1, 1, 0⟩, some 0), .expect 1), 1), (((⟨0, 2, 0⟩, some 1), .reply 0), 2),
  (((⟨1, 2, 0⟩, none), .reply 2), 1), (((⟨1, 2, 1⟩, none), .reply 1), 2),
  (((⟨0, 2, 0⟩, none), .reply 1), 1), (((⟨1, 2, 0⟩, some 2), .reply 1), 2),
  (((⟨1, 2, 0⟩, some 1), .reply 2), 1), (((⟨0, 2, 1⟩, some 0), .reply 1), 1),
  (((⟨0, 2, 2⟩, none), .reply 0), 2), (((⟨0, 2, 1⟩, none), .reply 0), 2),
  (((⟨0, 2, 0⟩, some 0), .reply 1), 1)]

theorem certCheck_certificate : certCheck configSteps bufferSteps certificate = true := by
  decide +kernel

/-- **Go-back-N with window 2 implements a two-place buffer**: over a lossy
one-place data channel, with timeouts and cumulative acknowledgements, the
protocol is weakly bisimilar to the empty two-place buffer. -/
theorem goBackN_weaklyBisimilar_buffer : lts.HomWeakBisimilarity goBackN buf :=
  weaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := 0) (by decide +kernel)

/-- The protocol is even observation congruent to the buffer. -/
theorem goBackN_observationCongruent_buffer :
    lts.RootedWeaklyBisimilar goBackN buf :=
  rootedWeaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := 0) (by decide +kernel)

/-! ## Lossy acknowledgements -/

/-- The internal channels of the lossy variant. -/
def lossyInternal : List Name := internal ++ [.reply 0, .reply 1, .reply 2]

/-- Configurations of the lossy variant: sender, data channel, receiver, and
acknowledgement channel. -/
abbrev LossyConfig := Config × Option ℕ

/-- The lossy variant in a configuration. -/
def lossySystem (c : LossyConfig) : Process Name Agent :=
  .restriction lossyInternal
    (.parallel
      (.parallel (.parallel (.constant (.sender c.1.1.1)) (.constant (.data c.1.1.2)))
        (.constant (.lossyReceiver c.1.2)))
      (.constant (.ackChannel c.2)))

/-- The configuration-level transitions of the lossy variant. -/
def lossyConfigSteps : LossyConfig → List (Label Name × LossyConfig) :=
  restrictSteps lossyInternal
    (parSteps (parSteps (parSteps senderSteps dataSteps) lossyReceiverSteps) ackChannelSteps)

theorem realizes_lossySystem : Realizes spec lossySystem lossyConfigSteps :=
  ((((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.lossyReceiver lossyReceiverSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.ackChannel ackChannelSteps fun _ => rfl)).restriction lossyInternal

/-- Go-back-N with a lossy acknowledgement channel. -/
def lossyGoBackN : Process Name Agent := lossySystem (initial, none)

/-- A step of the lossy variant read off its configuration transitions. -/
theorem lossy_step {c c' : LossyConfig} {a : Label Name} (h : (a, c') ∈ lossyConfigSteps c) :
    lts.Tr (lossySystem c) a (lossySystem c') :=
  (realizes_lossySystem c a _).2 ⟨c', h, rfl⟩

/-- The buffer takes no silent steps. -/
theorem buffer_silentClosure {n : ℕ} {Q : Process Name Agent}
    (h : lts.τSTr (buffer n) Q) : Q = buffer n := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      obtain ⟨m, hm, -⟩ := (realizes_buffer n _ _).1 hstep
      simp only [bufferSteps, List.mem_append] at hm
      split_ifs at hm <;> simp_all

/-- The visible weak steps of the buffer are its steps. -/
theorem buffer_weakStep {n : ℕ} {a : Label Name} {Q : Process Name Agent} (ha : a ≠ .tau)
    (h : lts.STr (buffer n) a Q) :
    ∃ m, (a, m) ∈ bufferSteps n ∧ Q = buffer m := by
  obtain ⟨before, after, hpre, hstep, hpost⟩ := (STr.iff_exists_of_ne ha).1 h
  rw [buffer_silentClosure hpre] at hstep
  obtain ⟨m, hm, rfl⟩ := (realizes_buffer n _ _).1 hstep
  exact ⟨m, hm, buffer_silentClosure hpost⟩

/-- The silent closure of the stuck configuration: the window is full (base
`0`, two outstanding), the receiver holds frame `1` to deliver, and the
acknowledgement of frame `0` was lost. -/
def stuckClosure : List LossyConfig :=
  [(((⟨0, 2, 2⟩, none), .deliver 1), none), (((⟨0, 2, 0⟩, none), .deliver 1), none),
   (((⟨0, 2, 1⟩, some 0), .deliver 1), none), (((⟨0, 2, 0⟩, some 0), .deliver 1), none),
   (((⟨0, 2, 1⟩, none), .deliver 1), none), (((⟨0, 2, 2⟩, some 1), .deliver 1), none),
   (((⟨0, 2, 0⟩, some 1), .deliver 1), none)]

theorem stuckClosure_closed : stuckClosure.all (fun c => (lossyConfigSteps c).all fun y =>
    y.1 != .tau || stuckClosure.contains y.2) = true := by
  decide +kernel

theorem stuckClosure_no_acc : stuckClosure.all (fun c => (lossyConfigSteps c).all fun y =>
    y.1 != .input .acc) = true := by
  decide +kernel

/-- No configuration silently reachable from the stuck one accepts. -/
theorem stuck_not_hasOutLabel_acc :
    ¬ lts.saturate.HasOutLabel (lossySystem (((⟨0, 2, 2⟩, none), .deliver 1), none))
      (.input .acc) := by
  rintro ⟨target, hweak⟩
  obtain ⟨before, after, hpre, hstep, -⟩ := (STr.iff_exists_of_ne (by simp)).1 hweak
  have hinv : ∀ Q, lts.τSTr
      (lossySystem (((⟨0, 2, 2⟩, none), .deliver 1), none)) Q →
      ∃ c ∈ stuckClosure, Q = lossySystem c := by
    intro Q hQ
    induction hQ with
    | refl => exact ⟨_, by decide, rfl⟩
    | tail _ hstep ih =>
        obtain ⟨c, hc, rfl⟩ := ih
        obtain ⟨c', hc', rfl⟩ := (realizes_lossySystem c _ _).1 hstep
        have h := stuckClosure_closed
        simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
          List.contains_iff_mem] at h
        exact ⟨c', (h c hc _ hc').resolve_left (fun hne => hne rfl), rfl⟩
  obtain ⟨c, hc, rfl⟩ := hinv before hpre
  obtain ⟨c', hc', -⟩ := (realizes_lossySystem c _ _).1 hstep
  have h := stuckClosure_no_acc
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h c hc _ hc' rfl

/-- **Lossy acknowledgements break the buffer specification**: with a lossy
acknowledgement channel and the deliver-then-acknowledge receiver, go-back-N is
not weakly bisimilar to the two-place buffer. Accept two messages, deliver the
first and lose its acknowledgement, and let the receiver take the second frame:
the buffer now holds one message and accepts another, but the protocol cannot
accept before it delivers. -/
theorem lossyGoBackN_not_weaklyBisimilar_buffer :
    ¬ lts.HomWeakBisimilarity lossyGoBackN buf := by
  intro hbisim
  -- accept, accept
  have h1 : lts.STr lossyGoBackN (.input .acc)
      (lossySystem (((⟨0, 1, 0⟩, none), .expect 0), none)) :=
    STr.single (lossy_step (by decide +kernel))
  have h2 : lts.STr (lossySystem (((⟨0, 1, 0⟩, none), .expect 0), none))
      (.input .acc) (lossySystem (((⟨0, 2, 0⟩, none), .expect 0), none)) :=
    STr.single (lossy_step (by decide +kernel))
  -- transmit and deliver frame 0, lose its acknowledgement, receive frame 1
  have h3 : lts.STr (lossySystem (((⟨0, 2, 0⟩, none), .expect 0), none))
      (.output .del) (lossySystem (((⟨0, 2, 2⟩, none), .deliver 1), none)) := by
    refine (STr.iff_exists_of_ne (by simp)).2
      ⟨lossySystem (((⟨0, 2, 1⟩, none), .deliver 0), none),
        lossySystem (((⟨0, 2, 1⟩, none), .reply 1), none), ?_, lossy_step (by decide +kernel), ?_⟩
    · exact τSTr.cons (lossy_step (c' := (((⟨0, 2, 1⟩, some 0), .expect 0), none))
        (by decide +kernel)) (τSTr.of_tr (lossy_step (by decide +kernel)))
    · refine τSTr.cons
        (lossy_step (c' := (((⟨0, 2, 1⟩, none), .expect 1), some 1)) (by decide +kernel)) ?_
      refine τSTr.cons
        (lossy_step (c' := (((⟨0, 2, 1⟩, none), .expect 1), none)) (by decide +kernel)) ?_
      exact τSTr.cons
        (lossy_step (c' := (((⟨0, 2, 2⟩, some 1), .expect 1), none)) (by decide +kernel))
        (τSTr.of_tr (lossy_step (by decide +kernel)))
  obtain ⟨Q1, hQ1, hb1⟩ := hbisim.sTr h1
  obtain ⟨m1, hm1, rfl⟩ := buffer_weakStep (by simp) hQ1
  obtain ⟨Q2, hQ2, hb2⟩ := hb1.sTr h2
  obtain ⟨m2, hm2, rfl⟩ := buffer_weakStep (by simp) hQ2
  obtain ⟨Q3, hQ3, hb3⟩ := hb2.sTr h3
  obtain ⟨m3, hm3, rfl⟩ := buffer_weakStep (by simp) hQ3
  obtain rfl : m1 = 1 := by simpa [bufferSteps] using hm1
  obtain rfl : m2 = 2 := by simpa [bufferSteps] using hm2
  obtain rfl : m3 = 1 := by simpa [bufferSteps] using hm3
  exact stuck_not_hasOutLabel_acc ((hb3.hasOutLabel_saturate_iff _).2
    ⟨buffer 2, STr.single ((realizes_buffer 1 _ _).2 ⟨2, by simp [bufferSteps], rfl⟩)⟩)

end Cslib.Algorithms.CCS.GoBackN
