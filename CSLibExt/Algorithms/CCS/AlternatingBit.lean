/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The alternating-bit protocol
-/
module

public import CSLibExt.Algorithms.CCS.FiniteState

/-!
# The alternating-bit protocol over lossy channels

The alternating-bit protocol (Bartlett, Scantlebury and Wilkinson, *A note on
reliable full-duplex transmission over half-duplex links*, CACM 12, 1969), after
the CCS treatment of Milner (*Communication and Concurrency*, Prentice Hall,
1989, Sections 6.3-6.4), in a bounded, loss-only, data-free variant:

* Milner's channels are unbounded buffers that may both lose and duplicate
  messages, and his receiver also retransmits on a timeout. Here both channels
  hold at most one item and may only lose it; duplicates arise only from the
  sender's retransmissions, and only the sender has a timeout.
* `acc` and `del` carry no payload, so the theorem is about the control flow of
  the protocol: accepts and deliveries alternate. It does not track message
  contents.

* The sender accepts a message (`acc`), transmits a frame tagged with its
  current bit, and waits. An acknowledgement carrying its bit lets it flip the
  bit and accept the next message; a stale acknowledgement is ignored; a silent
  timeout makes it retransmit.
* The data channel and the acknowledgement channel each hold at most one item
  and may silently lose it.
* The receiver, expecting bit `b`, delivers (`del`) a frame tagged `b` and
  acknowledges it, then expects `!b`; a frame tagged `!b` is a duplicate and is
  only acknowledged again.

The protocol `abp` is the parallel composition of the four agents with every
internal channel restricted. The main theorem `abp_weaklyBisimilar_buffer`:
`abp` is weakly bisimilar (observation equivalent) to the one-place buffer
`buf = acc.del.buf`. Losses and retransmissions are silent, so an observer sees
exactly an alternation of accepts and deliveries, starting with an accept.
Since neither process can move silently at the start, they are even
observation congruent (`abp_observationCongruent_buffer`).

The proof is a finite certificate: the 108 pairs of reachable protocol
configuration and buffer state, checked by `certCheck` from
`FiniteState.lean` with `decide +kernel`. The list is sorted by silent distance
to the next visible action, which the backward check uses as a ranking.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.AlternatingBit

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

/-- Channel names: the user interface `acc` and `del`, and the internal
channels, each in two versions tagged by a bit. -/
inductive Name
  /-- Accept a message from the user. -/
  | acc
  /-- Deliver a message to the user. -/
  | del
  /-- Sender to data channel. -/
  | send (b : Bool)
  /-- Data channel to receiver. -/
  | recv (b : Bool)
  /-- Receiver to acknowledgement channel. -/
  | reply (b : Bool)
  /-- Acknowledgement channel to sender. -/
  | ack (b : Bool)
  deriving DecidableEq

/-- Sender states. -/
inductive Sender
  /-- Ready to accept a message, to be sent with this bit. -/
  | accept (b : Bool)
  /-- About to transmit a frame with this bit. -/
  | transmit (b : Bool)
  /-- Waiting for the acknowledgement of this bit. -/
  | await (b : Bool)
  deriving DecidableEq

/-- States of a one-place channel. -/
inductive Channel
  | empty
  | full (b : Bool)
  deriving DecidableEq

/-- Receiver states. -/
inductive Receiver
  /-- Expecting a frame with this bit. -/
  | expect (b : Bool)
  /-- About to deliver the message of a frame with this bit. -/
  | deliver (b : Bool)
  /-- About to acknowledge this bit. -/
  | reply (b : Bool)
  deriving DecidableEq

/-- Sender transitions. -/
def senderSteps : Sender → List (Label Name × Sender)
  | .accept b => [(.input .acc, .transmit b)]
  | .transmit b => [(.output (.send b), .await b)]
  | .await b =>
      [(.input (.ack b), .accept (!b)), (.input (.ack (!b)), .await b), (.tau, .transmit b)]

/-- Lossy one-place data channel. -/
def dataSteps : Channel → List (Label Name × Channel)
  | .empty => [(.input (.send false), .full false), (.input (.send true), .full true)]
  | .full b => [(.output (.recv b), .empty), (.tau, .empty)]

/-- Receiver transitions. -/
def receiverSteps : Receiver → List (Label Name × Receiver)
  | .expect b => [(.input (.recv b), .deliver b), (.input (.recv (!b)), .reply (!b))]
  | .deliver b => [(.output .del, .reply b)]
  | .reply b => [(.output (.reply b), .expect (!b))]

/-- Lossy one-place acknowledgement channel. -/
def ackSteps : Channel → List (Label Name × Channel)
  | .empty => [(.input (.reply false), .full false), (.input (.reply true), .full true)]
  | .full b => [(.output (.ack b), .empty), (.tau, .empty)]

/-- The one-place buffer: empty (`false`) or full (`true`). -/
def bufferSteps : Bool → List (Label Name × Bool)
  | false => [(.input .acc, true)]
  | true => [(.output .del, false)]

/-- Process constants: one per state of each agent. -/
inductive Agent
  | sender (s : Sender)
  | data (c : Channel)
  | receiver (r : Receiver)
  | ack (c : Channel)
  | buffer (full : Bool)

/-- The recursive specification: each constant is the choice of its listed
transitions. -/
def spec : Specification Name Agent
  | .sender s => sumOf ((senderSteps s).map fun y => (y.1, .constant (.sender y.2)))
  | .data c => sumOf ((dataSteps c).map fun y => (y.1, .constant (.data y.2)))
  | .receiver r => sumOf ((receiverSteps r).map fun y => (y.1, .constant (.receiver y.2)))
  | .ack c => sumOf ((ackSteps c).map fun y => (y.1, .constant (.ack y.2)))
  | .buffer b => sumOf ((bufferSteps b).map fun y => (y.1, .constant (.buffer y.2)))

/-- The labelled transition system of the specification. -/
abbrev lts : LTS (Process Name Agent) (Label Name) := Process.lts spec

/-- The internal channels, all restricted. -/
def internal : List Name :=
  [.send false, .send true, .recv false, .recv true, .reply false, .reply true,
    .ack false, .ack true]

/-- Protocol configurations: sender, data channel, receiver, acknowledgement
channel. -/
abbrev Config := ((Sender × Channel) × Receiver) × Channel

/-- The protocol process in a configuration. -/
def system (c : Config) : Process Name Agent :=
  .restriction internal
    (.parallel (.parallel (.parallel (.constant (.sender c.1.1.1)) (.constant (.data c.1.1.2)))
      (.constant (.receiver c.1.2))) (.constant (.ack c.2)))

/-- The configuration-level transitions of the protocol. -/
def configSteps : Config → List (Label Name × Config) :=
  restrictSteps internal (parSteps (parSteps (parSteps senderSteps dataSteps) receiverSteps)
    ackSteps)

theorem realizes_system : Realizes spec system configSteps :=
  ((((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.receiver receiverSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.ack ackSteps fun _ => rfl)).restriction internal

/-- The buffer process. -/
def buffer (full : Bool) : Process Name Agent := .constant (.buffer full)

theorem realizes_buffer : Realizes spec buffer bufferSteps :=
  Realizes.constant Agent.buffer bufferSteps fun _ => rfl

/-- The initial configuration: the sender ready to accept with bit `false`, both
channels empty, the receiver expecting bit `false`. -/
def initial : Config := (((.accept false, .empty), .expect false), .empty)

/-- The alternating-bit protocol. -/
def abp : Process Name Agent := system initial

/-- The one-place buffer `buf = acc.del.buf`. -/
def buf : Process Name Agent := buffer false

/-- The weak-bisimulation certificate: every reachable configuration, paired
with the buffer state it simulates (`true` from the accept of a message until
its delivery), sorted by silent distance to the next visible action. -/
def certificate : List (Config × Bool) := [
  (((((.accept false), (.full true)), (.expect false)), (.full true)), false),
  (((((.accept false), (.full true)), (.expect false)), .empty), false),
  (((((.accept false), (.full true)), (.reply true)), .empty), false),
  (((((.accept false), .empty), (.expect false)), (.full true)), false),
  (((((.accept false), .empty), (.expect false)), .empty), false),
  (((((.accept false), .empty), (.reply true)), (.full true)), false),
  (((((.accept false), .empty), (.reply true)), .empty), false),
  (((((.accept true), (.full false)), (.expect true)), (.full false)), false),
  (((((.accept true), (.full false)), (.expect true)), .empty), false),
  (((((.accept true), (.full false)), (.reply false)), .empty), false),
  (((((.accept true), .empty), (.expect true)), (.full false)), false),
  (((((.accept true), .empty), (.expect true)), .empty), false),
  (((((.accept true), .empty), (.reply false)), (.full false)), false),
  (((((.accept true), .empty), (.reply false)), .empty), false),
  (((((.await false), (.full false)), (.expect true)), (.full false)), false),
  (((((.await false), (.full false)), (.reply false)), (.full false)), false),
  (((((.await false), .empty), (.expect true)), (.full false)), false),
  (((((.await false), .empty), (.reply false)), (.full false)), false),
  (((((.await true), (.full true)), (.expect false)), (.full true)), false),
  (((((.await true), (.full true)), (.reply true)), (.full true)), false),
  (((((.await true), .empty), (.expect false)), (.full true)), false),
  (((((.await true), .empty), (.reply true)), (.full true)), false),
  (((((.await false), (.full false)), (.reply false)), .empty), false),
  (((((.await false), .empty), (.reply false)), .empty), false),
  (((((.await true), (.full true)), (.reply true)), .empty), false),
  (((((.await true), .empty), (.reply true)), .empty), false),
  (((((.transmit false), .empty), (.expect true)), (.full false)), false),
  (((((.transmit false), .empty), (.reply false)), (.full false)), false),
  (((((.transmit true), .empty), (.expect false)), (.full true)), false),
  (((((.transmit true), .empty), (.reply true)), (.full true)), false),
  (((((.await false), (.full false)), (.expect true)), .empty), false),
  (((((.await false), (.full false)), (.reply false)), (.full true)), false),
  (((((.await false), .empty), (.reply false)), (.full true)), false),
  (((((.await true), (.full true)), (.expect false)), .empty), false),
  (((((.await true), (.full true)), (.reply true)), (.full false)), false),
  (((((.await true), .empty), (.reply true)), (.full false)), false),
  (((((.transmit false), (.full false)), (.expect true)), (.full false)), false),
  (((((.transmit false), (.full false)), (.reply false)), (.full false)), false),
  (((((.transmit false), .empty), (.reply false)), .empty), false),
  (((((.transmit true), (.full true)), (.expect false)), (.full true)), false),
  (((((.transmit true), (.full true)), (.reply true)), (.full true)), false),
  (((((.transmit true), .empty), (.reply true)), .empty), false),
  (((((.transmit false), (.full false)), (.expect true)), .empty), false),
  (((((.transmit false), (.full false)), (.reply false)), .empty), false),
  (((((.transmit false), .empty), (.expect true)), .empty), false),
  (((((.transmit false), .empty), (.reply false)), (.full true)), false),
  (((((.transmit true), (.full true)), (.expect false)), .empty), false),
  (((((.transmit true), (.full true)), (.reply true)), .empty), false),
  (((((.transmit true), .empty), (.expect false)), .empty), false),
  (((((.transmit true), .empty), (.reply true)), (.full false)), false),
  (((((.await false), .empty), (.expect true)), .empty), false),
  (((((.await true), .empty), (.expect false)), .empty), false),
  (((((.transmit false), (.full false)), (.reply false)), (.full true)), false),
  (((((.transmit true), (.full true)), (.reply true)), (.full false)), false),
  (((((.await false), (.full false)), (.deliver false)), (.full true)), true),
  (((((.await false), (.full false)), (.deliver false)), .empty), true),
  (((((.await false), .empty), (.deliver false)), (.full true)), true),
  (((((.await false), .empty), (.deliver false)), .empty), true),
  (((((.await true), (.full true)), (.deliver true)), (.full false)), true),
  (((((.await true), (.full true)), (.deliver true)), .empty), true),
  (((((.await true), .empty), (.deliver true)), (.full false)), true),
  (((((.await true), .empty), (.deliver true)), .empty), true),
  (((((.transmit false), (.full false)), (.deliver false)), (.full true)), true),
  (((((.transmit false), (.full false)), (.deliver false)), .empty), true),
  (((((.transmit false), .empty), (.deliver false)), (.full true)), true),
  (((((.transmit false), .empty), (.deliver false)), .empty), true),
  (((((.transmit true), (.full true)), (.deliver true)), (.full false)), true),
  (((((.transmit true), (.full true)), (.deliver true)), .empty), true),
  (((((.transmit true), .empty), (.deliver true)), (.full false)), true),
  (((((.transmit true), .empty), (.deliver true)), .empty), true),
  (((((.await false), (.full false)), (.expect false)), (.full true)), true),
  (((((.await false), (.full false)), (.expect false)), .empty), true),
  (((((.await true), (.full true)), (.expect true)), (.full false)), true),
  (((((.await true), (.full true)), (.expect true)), .empty), true),
  (((((.transmit false), (.full false)), (.expect false)), (.full true)), true),
  (((((.transmit false), (.full false)), (.expect false)), .empty), true),
  (((((.transmit true), (.full true)), (.expect true)), (.full false)), true),
  (((((.transmit true), (.full true)), (.expect true)), .empty), true),
  (((((.await false), (.full false)), (.reply true)), .empty), true),
  (((((.await true), (.full true)), (.reply false)), .empty), true),
  (((((.transmit false), (.full false)), (.reply true)), .empty), true),
  (((((.transmit false), .empty), (.expect false)), (.full true)), true),
  (((((.transmit false), .empty), (.expect false)), .empty), true),
  (((((.transmit true), (.full true)), (.reply false)), .empty), true),
  (((((.transmit true), .empty), (.expect true)), (.full false)), true),
  (((((.transmit true), .empty), (.expect true)), .empty), true),
  (((((.await false), (.full false)), (.reply true)), (.full true)), true),
  (((((.await false), .empty), (.expect false)), (.full true)), true),
  (((((.await false), .empty), (.expect false)), .empty), true),
  (((((.await true), (.full true)), (.reply false)), (.full false)), true),
  (((((.await true), .empty), (.expect true)), (.full false)), true),
  (((((.await true), .empty), (.expect true)), .empty), true),
  (((((.transmit false), (.full false)), (.reply true)), (.full true)), true),
  (((((.transmit false), (.full true)), (.expect false)), (.full true)), true),
  (((((.transmit false), .empty), (.reply true)), .empty), true),
  (((((.transmit true), (.full false)), (.expect true)), (.full false)), true),
  (((((.transmit true), (.full false)), (.expect true)), .empty), true),
  (((((.transmit true), (.full true)), (.reply false)), (.full false)), true),
  (((((.transmit true), .empty), (.reply false)), .empty), true),
  (((((.await false), .empty), (.reply true)), .empty), true),
  (((((.await true), .empty), (.reply false)), .empty), true),
  (((((.transmit false), (.full true)), (.expect false)), .empty), true),
  (((((.transmit false), (.full true)), (.reply true)), .empty), true),
  (((((.transmit false), .empty), (.reply true)), (.full true)), true),
  (((((.transmit true), (.full false)), (.reply false)), .empty), true),
  (((((.transmit true), .empty), (.reply false)), (.full false)), true),
  (((((.await false), .empty), (.reply true)), (.full true)), true),
  (((((.await true), .empty), (.reply false)), (.full false)), true)]

theorem certCheck_certificate : certCheck configSteps bufferSteps certificate = true := by
  decide +kernel

/-- **The alternating-bit protocol implements a one-place buffer**: over lossy
one-place channels, `abp` is weakly bisimilar to `buf = acc.del.buf`. -/
theorem abp_weaklyBisimilar_buffer : lts.HomWeakBisimilarity abp buf :=
  weaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := false) (by decide +kernel)

/-- The protocol is even observation congruent (rooted weakly bisimilar) to
the buffer: initially neither side can move silently. -/
theorem abp_observationCongruent_buffer : lts.RootedWeaklyBisimilar abp buf :=
  rootedWeaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := false) (by decide +kernel)

end Cslib.Algorithms.CCS.AlternatingBit
