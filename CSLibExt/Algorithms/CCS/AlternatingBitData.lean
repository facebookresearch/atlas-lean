/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The alternating-bit protocol with data
-/
module

public import CSLibExt.Algorithms.CCS.FiniteState

/-!
# The alternating-bit protocol with data

The alternating-bit protocol of `AlternatingBit.lean` with a one-bit message
payload. There `acc` and `del` carry nothing, so the theorem only says that
accepts and deliveries alternate. Here the user hands over a bit with `acc d`,
frames carry it alongside the sequence bit, and the receiver hands it out with
`del d`. The theorem `abpData_weaklyBisimilar_buffer` says that the protocol is
weakly bisimilar, indeed observation congruent
(`abpData_observationCongruent_buffer`), to the one-place buffer of bits: every
delivered bit is the bit accepted last, no bit is delivered twice, and losses
and retransmissions are invisible. Weak bisimilarity does not see divergence:
the channels may lose every frame forever, so the theorem says nothing about
eventual delivery, which needs a fairness assumption on the channels.

The rest of the model is as in `AlternatingBit.lean` (after Milner,
*Communication and Concurrency*, 1989, Sections 6.3-6.4): one-place channels
that may lose but not duplicate, and a timeout on the sender only.

The proof is a 220-pair certificate (every reachable configuration with the
buffer content it simulates), checked by `certCheck` from `FiniteState.lean`
with `decide +kernel`.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.AlternatingBitData

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

/-- Channel names; `b` is a sequence bit and `d` a data bit. -/
inductive Name
  /-- Accept a data bit from the user. -/
  | acc (d : Bool)
  /-- Deliver a data bit to the user. -/
  | del (d : Bool)
  /-- Sender to data channel. -/
  | send (b d : Bool)
  /-- Data channel to receiver. -/
  | recv (b d : Bool)
  /-- Receiver to acknowledgement channel. -/
  | reply (b : Bool)
  /-- Acknowledgement channel to sender. -/
  | ack (b : Bool)
  deriving DecidableEq

/-- Sender states. -/
inductive Sender
  /-- Ready to accept a message, to be sent with sequence bit `b`. -/
  | accept (b : Bool)
  /-- About to transmit data `d` with sequence bit `b`. -/
  | transmit (b d : Bool)
  /-- Waiting for the acknowledgement of `b`, holding `d` for retransmission. -/
  | await (b d : Bool)
  deriving DecidableEq

/-- Receiver states. -/
inductive Receiver
  /-- Expecting a frame with sequence bit `b`. -/
  | expect (b : Bool)
  /-- About to deliver data `d` of a frame with sequence bit `b`. -/
  | deliver (b d : Bool)
  /-- About to acknowledge `b`. -/
  | reply (b : Bool)
  deriving DecidableEq

/-- Sender transitions. -/
def senderSteps : Sender → List (Label Name × Sender)
  | .accept b => [(.input (.acc false), .transmit b false), (.input (.acc true), .transmit b true)]
  | .transmit b d => [(.output (.send b d), .await b d)]
  | .await b d =>
      [(.input (.ack b), .accept (!b)), (.input (.ack (!b)), .await b d), (.tau, .transmit b d)]

/-- Lossy one-place data channel, holding a sequence bit and a data bit. -/
def dataSteps : Option (Bool × Bool) → List (Label Name × Option (Bool × Bool))
  | none => [false, true].flatMap fun b => [false, true].map fun d =>
      (.input (.send b d), some (b, d))
  | some (b, d) => [(.output (.recv b d), none), (.tau, none)]

/-- Receiver transitions: deliver the data of an expected frame, acknowledge a
duplicate again. -/
def receiverSteps : Receiver → List (Label Name × Receiver)
  | .expect b => [false, true].flatMap fun d =>
      [(.input (.recv b d), .deliver b d), (.input (.recv (!b) d), .reply (!b))]
  | .deliver b d => [(.output (.del d), .reply b)]
  | .reply b => [(.output (.reply b), .expect (!b))]

/-- Lossy one-place acknowledgement channel. -/
def ackSteps : Option Bool → List (Label Name × Option Bool)
  | none => [(.input (.reply false), some false), (.input (.reply true), some true)]
  | some b => [(.output (.ack b), none), (.tau, none)]

/-- The one-place buffer of bits: empty (`none`) or holding a bit. -/
def bufferSteps : Option Bool → List (Label Name × Option Bool)
  | none => [(.input (.acc false), some false), (.input (.acc true), some true)]
  | some d => [(.output (.del d), none)]

/-- Process constants: one per state of each agent. -/
inductive Agent
  | sender (s : Sender)
  | data (c : Option (Bool × Bool))
  | receiver (r : Receiver)
  | ack (c : Option Bool)
  | buffer (content : Option Bool)

/-- The recursive specification: each constant is the choice of its listed
transitions. -/
def spec : Specification Name Agent
  | .sender s => sumOf ((senderSteps s).map fun y => (y.1, .constant (.sender y.2)))
  | .data c => sumOf ((dataSteps c).map fun y => (y.1, .constant (.data y.2)))
  | .receiver r => sumOf ((receiverSteps r).map fun y => (y.1, .constant (.receiver y.2)))
  | .ack c => sumOf ((ackSteps c).map fun y => (y.1, .constant (.ack y.2)))
  | .buffer q => sumOf ((bufferSteps q).map fun y => (y.1, .constant (.buffer y.2)))

/-- The labelled transition system of the specification. -/
abbrev lts : LTS (Process Name Agent) (Label Name) := Process.lts spec

/-- The internal channels, all restricted. -/
def internal : List Name :=
  ([false, true].flatMap fun b => [false, true].flatMap fun d => [.send b d, .recv b d]) ++
    [.reply false, .reply true, .ack false, .ack true]

/-- Protocol configurations: sender, data channel, receiver, acknowledgement
channel. -/
abbrev Config := ((Sender × Option (Bool × Bool)) × Receiver) × Option Bool

/-- The protocol process in a configuration. -/
def system (c : Config) : Process Name Agent :=
  .restriction internal
    (.parallel
      (.parallel (.parallel (.constant (.sender c.1.1.1)) (.constant (.data c.1.1.2)))
        (.constant (.receiver c.1.2)))
      (.constant (.ack c.2)))

/-- The configuration-level transitions of the protocol. -/
def configSteps : Config → List (Label Name × Config) :=
  restrictSteps internal
    (parSteps (parSteps (parSteps senderSteps dataSteps) receiverSteps) ackSteps)

theorem realizes_system : Realizes spec system configSteps :=
  ((((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.receiver receiverSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.ack ackSteps fun _ => rfl)).restriction internal

/-- The buffer process with the given content. -/
def buffer (q : Option Bool) : Process Name Agent := .constant (.buffer q)

theorem realizes_buffer : Realizes spec buffer bufferSteps :=
  Realizes.constant Agent.buffer bufferSteps fun _ => rfl

/-- The initial configuration: sender ready with bit `false`, channels empty,
receiver expecting `false`. -/
def initial : Config := (((.accept false, none), .expect false), none)

/-- The alternating-bit protocol with data. -/
def abpData : Process Name Agent := system initial

/-- The empty one-place buffer of bits. -/
def buf : Process Name Agent := buffer none

/-- The weak-bisimulation certificate: every reachable configuration with the
buffer content it simulates, listed so that every pair reaches the visible
actions of its buffer state through pairs listed earlier. -/
def certificate : List (Config × Option Bool) := [
  ((((.accept true, none), .expect true), some false), none),
  ((((.transmit false true, none), .deliver false true), none), some true),
  ((((.transmit false true, none), .deliver false true), some true), some true),
  ((((.accept true, none), .reply false), some false), none),
  ((((.await false true, some (false, true)), .deliver false true), none), some true),
  ((((.await false true, some (false, true)), .deliver false true), some true), some true),
  ((((.transmit true false, some (true, false)), .deliver true false), none), some false),
  ((((.accept true, some (false, false)), .reply false), none), none),
  ((((.await true false, none), .deliver true false), some false), some false),
  ((((.accept true, none), .expect true), none), none),
  ((((.accept false, some (true, true)), .expect false), none), none),
  ((((.transmit false true, some (false, true)), .expect false), some true), some true),
  ((((.accept false, none), .reply true), some true), none),
  ((((.transmit false true, some (false, true)), .expect false), none), some true),
  ((((.transmit true false, none), .deliver true false), none), some false),
  ((((.accept false, some (true, false)), .reply true), none), none),
  ((((.transmit false true, some (false, true)), .reply true), none), some true),
  ((((.accept false, some (true, true)), .expect false), some true), none),
  ((((.transmit false false, some (false, false)), .deliver false false), some true), some false),
  ((((.accept true, some (false, false)), .expect true), some false), none),
  ((((.accept false, some (true, false)), .expect false), none), none),
  ((((.accept true, some (false, false)), .expect true), none), none),
  ((((.transmit true true, some (true, true)), .deliver true true), none), some true),
  ((((.await false true, none), .deliver false true), none), some true),
  ((((.transmit true false, some (true, false)), .expect true), none), some false),
  ((((.await false false, none), .expect true), some false), none),
  ((((.await true false, none), .deliver true false), none), some false),
  ((((.transmit false true, some (false, true)), .deliver false true), some true), some true),
  ((((.await true false, some (true, false)), .expect false), some true), none),
  ((((.await false false, none), .deliver false false), none), some false),
  ((((.accept true, some (false, true)), .expect true), none), none),
  ((((.accept false, some (true, false)), .expect false), some true), none),
  ((((.await false false, none), .deliver false false), some true), some false),
  ((((.await false true, none), .deliver false true), some true), some true),
  ((((.await true false, some (true, false)), .deliver true false), some false), some false),
  ((((.accept false, none), .reply true), none), none),
  ((((.transmit true false, some (true, false)), .expect true), some false), some false),
  ((((.transmit false false, none), .deliver false false), none), some false),
  ((((.accept true, some (false, true)), .reply false), none), none),
  ((((.transmit false true, some (false, true)), .deliver false true), none), some true),
  ((((.await false true, none), .expect true), some false), none),
  ((((.await false false, some (false, false)), .deliver false false), some true), some false),
  ((((.accept false, none), .expect false), none), none),
  ((((.await false true, some (false, true)), .expect false), none), some true),
  ((((.await true true, none), .reply true), some true), none),
  ((((.accept true, some (false, true)), .expect true), some false), none),
  ((((.transmit true false, none), .expect false), some true), none),
  ((((.transmit true false, none), .deliver true false), some false), some false),
  ((((.transmit false false, some (false, false)), .deliver false false), none), some false),
  ((((.accept false, none), .expect false), some true), none),
  ((((.await false true, some (false, true)), .expect false), some true), some true),
  ((((.await false false, some (false, false)), .reply false), some false), none),
  ((((.transmit false false, none), .deliver false false), some true), some false),
  ((((.transmit true false, some (true, false)), .expect false), some true), none),
  ((((.transmit true true, some (true, true)), .deliver true true), some false), some true),
  ((((.await true false, some (true, false)), .deliver true false), none), some false),
  ((((.await true false, some (true, false)), .reply true), some true), none),
  ((((.transmit true true, none), .deliver true true), some false), some true),
  ((((.transmit true true, none), .deliver true true), none), some true),
  ((((.transmit false true, none), .expect false), none), some true),
  ((((.await false false, some (false, false)), .deliver false false), none), some false),
  ((((.transmit false true, some (false, true)), .reply true), some true), some true),
  ((((.await true true, some (true, true)), .deliver true true), some false), some true),
  ((((.await false true, some (false, true)), .expect true), some false), none),
  ((((.accept false, some (true, true)), .reply true), none), none),
  ((((.transmit false true, none), .expect false), some true), some true),
  ((((.await false true, some (false, true)), .reply false), none), none),
  ((((.await true false, none), .reply true), some true), none),
  ((((.await false true, some (false, true)), .reply false), some false), none),
  ((((.await true true, some (true, true)), .deliver true true), none), some true),
  ((((.await false false, some (false, false)), .expect true), some false), none),
  ((((.await true true, none), .deliver true true), some false), some true),
  ((((.transmit true false, some (true, false)), .deliver true false), some false), some false),
  ((((.await true true, none), .deliver true true), none), some true),
  ((((.transmit true true, some (true, true)), .expect true), some false), some true),
  ((((.accept true, none), .reply false), none), none),
  ((((.await false false, some (false, false)), .expect false), none), some false),
  ((((.await true true, some (true, true)), .expect true), some false), some true),
  ((((.transmit false false, some (false, false)), .expect false), none), some false),
  ((((.transmit true true, some (true, true)), .expect true), none), some true),
  ((((.transmit false true, none), .reply true), none), some true),
  ((((.await true true, some (true, true)), .expect false), some true), none),
  ((((.transmit true true, some (true, true)), .reply false), none), some true),
  ((((.await true true, none), .expect false), some true), none),
  ((((.await false true, none), .reply true), none), some true),
  ((((.await false true, none), .reply false), some false), none),
  ((((.await true false, some (true, false)), .expect true), some false), some false),
  ((((.transmit false false, none), .reply false), some false), none),
  ((((.transmit true true, none), .expect true), some false), some true),
  ((((.await false false, none), .reply false), none), none),
  ((((.await true false, some (true, false)), .reply true), none), none),
  ((((.transmit true false, none), .reply true), none), none),
  ((((.await false false, some (false, false)), .expect false), some true), some false),
  ((((.await true true, some (true, true)), .expect true), none), some true),
  ((((.await false true, some (false, true)), .reply true), none), some true),
  ((((.transmit false false, some (false, false)), .expect false), some true), some false),
  ((((.transmit true false, none), .reply true), some true), none),
  ((((.transmit true true, none), .reply false), none), some true),
  ((((.await false true, some (false, true)), .reply true), some true), some true),
  ((((.await true false, none), .expect false), some true), none),
  ((((.await true false, some (true, false)), .expect true), none), some false),
  ((((.await true true, none), .expect true), some false), some true),
  ((((.await false true, none), .expect false), some true), some true),
  ((((.transmit true true, some (false, true)), .expect true), none), some true),
  ((((.transmit true false, none), .expect true), none), some false),
  ((((.await true true, none), .reply true), none), none),
  ((((.transmit false true, some (true, true)), .expect false), none), some true),
  ((((.transmit true false, none), .expect true), some false), some false),
  ((((.await false true, none), .reply false), none), none),
  ((((.transmit false true, some (true, false)), .expect false), none), some true),
  ((((.await false true, none), .reply false), some true), none),
  ((((.transmit false true, some (true, true)), .expect false), some true), some true),
  ((((.transmit false true, some (true, false)), .expect false), some true), some true),
  ((((.await false true, some (false, true)), .reply false), some true), none),
  ((((.await true true, some (true, true)), .reply true), none), none),
  ((((.transmit true false, some (true, false)), .reply true), none), none),
  ((((.await false true, none), .expect false), none), some true),
  ((((.transmit true false, some (false, true)), .expect true), none), some false),
  ((((.await true true, some (true, true)), .reply true), some true), none),
  ((((.transmit false true, none), .reply true), some true), some true),
  ((((.transmit false false, some (false, false)), .reply false), some false), none),
  ((((.await true false, none), .expect true), some false), some false),
  ((((.await false false, none), .reply false), some false), none),
  ((((.transmit true false, some (true, false)), .reply false), none), some false),
  ((((.transmit false true, none), .reply false), some false), none),
  ((((.transmit true false, some (true, false)), .reply true), some true), none),
  ((((.transmit false true, some (true, true)), .reply true), none), some true),
  ((((.transmit false true, none), .reply false), none), none),
  ((((.transmit true true, some (false, false)), .expect true), some false), some true),
  ((((.await false false, some (false, false)), .reply true), none), some false),
  ((((.transmit false true, some (false, true)), .reply false), none), none),
  ((((.transmit false true, some (false, true)), .expect true), some false), none),
  ((((.await false false, some (false, false)), .reply true), some true), some false),
  ((((.transmit true true, some (false, false)), .expect true), none), some true),
  ((((.transmit false true, none), .reply false), some true), none),
  ((((.transmit false false, none), .expect true), some false), none),
  ((((.transmit false false, none), .reply true), none), some false),
  ((((.transmit true true, none), .reply true), some true), none),
  ((((.transmit false true, none), .expect true), some false), none),
  ((((.transmit false false, none), .expect false), none), some false),
  ((((.await false false, some (false, false)), .reply false), none), none),
  ((((.await true false, none), .expect true), none), some false),
  ((((.transmit false false, some (false, false)), .reply true), none), some false),
  ((((.transmit false true, some (false, true)), .expect true), none), none),
  ((((.transmit true false, some (true, false)), .expect false), none), none),
  ((((.await false false, some (false, false)), .reply false), some true), none),
  ((((.transmit false false, some (true, false)), .reply true), none), some false),
  ((((.await false false, none), .reply false), some true), none),
  ((((.transmit true true, some (true, true)), .reply false), some false), some true),
  ((((.transmit true true, some (false, true)), .reply false), none), some true),
  ((((.await true false, none), .reply true), none), none),
  ((((.await false false, none), .expect false), none), some false),
  ((((.transmit false false, none), .expect false), some true), some false),
  ((((.await false true, none), .reply true), some true), some true),
  ((((.transmit false false, some (false, false)), .expect true), some false), none),
  ((((.await false true, some (false, true)), .expect true), none), none),
  ((((.await true false, none), .reply false), none), some false),
  ((((.await true true, some (true, true)), .reply false), none), some true),
  ((((.transmit false true, some (true, false)), .reply true), none), some true),
  ((((.await false false, some (false, false)), .expect true), none), none),
  ((((.await true false, some (true, false)), .reply true), some false), none),
  ((((.transmit true true, none), .expect false), some true), none),
  ((((.transmit false false, some (true, true)), .expect false), some true), some false),
  ((((.transmit false false, some (true, false)), .expect false), some true), some false),
  ((((.transmit true false, none), .reply false), none), some false),
  ((((.transmit true true, some (false, true)), .expect true), some false), some true),
  ((((.transmit true false, some (false, true)), .reply false), none), some false),
  ((((.transmit true false, some (false, false)), .expect true), some false), some false),
  ((((.await true false, some (true, false)), .reply false), none), some false),
  ((((.transmit true false, none), .reply true), some false), none),
  ((((.transmit true true, none), .expect true), none), some true),
  ((((.await true true, some (true, true)), .expect false), none), none),
  ((((.await true true, none), .reply false), none), some true),
  ((((.await true true, some (true, true)), .reply false), some false), some true),
  ((((.await true false, some (true, false)), .reply false), some false), some false),
  ((((.transmit true false, none), .reply false), some false), some false),
  ((((.await false false, none), .reply true), none), some false),
  ((((.transmit true false, some (false, false)), .expect true), none), some false),
  ((((.transmit true false, some (false, true)), .expect true), some false), some false),
  ((((.transmit true true, none), .reply false), some false), some true),
  ((((.transmit true true, some (false, false)), .reply false), none), some true),
  ((((.await true true, none), .reply true), some false), none),
  ((((.transmit false false, some (true, true)), .reply true), none), some false),
  ((((.await true true, none), .expect true), none), some true),
  ((((.transmit true false, some (true, false)), .reply false), some false), some false),
  ((((.transmit true true, none), .reply true), none), none),
  ((((.await true false, some (true, false)), .expect false), none), none),
  ((((.await false false, none), .expect false), some true), some false),
  ((((.transmit false false, none), .reply true), some true), some false),
  ((((.await true true, some (true, true)), .reply true), some false), none),
  ((((.await false false, none), .reply true), some true), some false),
  ((((.transmit false false, none), .reply false), some true), none),
  ((((.transmit false true, some (false, true)), .reply false), some false), none),
  ((((.transmit true false, some (true, false)), .reply true), some false), none),
  ((((.transmit false true, some (false, true)), .reply false), some true), none),
  ((((.transmit true true, some (true, true)), .reply true), none), none),
  ((((.transmit false false, some (false, false)), .reply false), none), none),
  ((((.transmit false false, none), .reply false), none), none),
  ((((.transmit false false, some (true, false)), .expect false), none), some false),
  ((((.transmit false false, some (false, false)), .reply false), some true), none),
  ((((.transmit false false, some (false, false)), .reply true), some true), some false),
  ((((.transmit true true, some (true, true)), .expect false), some true), none),
  ((((.transmit true true, some (true, true)), .reply true), some true), none),
  ((((.transmit false false, some (true, true)), .expect false), none), some false),
  ((((.transmit false true, none), .expect true), none), none),
  ((((.await true false, none), .reply false), some false), some false),
  ((((.transmit true false, none), .expect false), none), none),
  ((((.await true false, none), .reply true), some false), none),
  ((((.transmit true true, none), .expect false), none), none),
  ((((.transmit false false, none), .expect true), none), none),
  ((((.transmit false false, some (false, false)), .expect true), none), none),
  ((((.transmit true false, some (false, false)), .reply false), none), some false),
  ((((.transmit true true, some (true, true)), .expect false), none), none),
  ((((.await true true, none), .expect false), none), none),
  ((((.await true true, none), .reply false), some false), some true),
  ((((.await true false, none), .expect false), none), none),
  ((((.transmit true true, none), .reply true), some false), none),
  ((((.transmit true true, some (true, true)), .reply true), some false), none),
  ((((.await false false, none), .expect true), none), none),
  ((((.await false true, none), .expect true), none), none)]

theorem certCheck_certificate : certCheck configSteps bufferSteps certificate = true := by
  decide +kernel

/-- **The alternating-bit protocol transmits data correctly**: it is weakly
bisimilar to the empty one-place buffer of bits. -/
theorem abpData_weaklyBisimilar_buffer : lts.HomWeakBisimilarity abpData buf :=
  weaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := none) (by decide +kernel)

/-- The protocol is even observation congruent to the buffer. -/
theorem abpData_observationCongruent_buffer :
    lts.RootedWeaklyBisimilar abpData buf :=
  rootedWeaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := none) (by decide +kernel)

end Cslib.Algorithms.CCS.AlternatingBitData
