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

/-- **Channel names of the alternating-bit protocol with data.** For bits $b$ and $d$, where $b$ is
a sequence bit and $d$ a data bit, the channel names are $\mathsf{acc}(d)$ (accept the data bit
$d$ from the user), $\mathsf{del}(d)$ (deliver the data bit $d$ to the user), $\mathsf{send}(b, d)$
(sender to data channel), $\mathsf{recv}(b, d)$ (data channel to receiver), $\mathsf{reply}(b)$
(receiver to acknowledgement channel) and $\mathsf{ack}(b)$ (acknowledgement channel to sender). -/
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

/-- **Sender states of the alternating-bit protocol with data.** For bits $b$ and $d$, a sender
state is $\mathsf{accept}(b)$, ready to accept a message to be sent with sequence bit $b$;
$\mathsf{transmit}(b, d)$, about to transmit the data bit $d$ with sequence bit $b$; or
$\mathsf{await}(b, d)$, waiting for the acknowledgement of $b$ while holding $d$ for
retransmission. -/
inductive Sender
  /-- Ready to accept a message, to be sent with sequence bit `b`. -/
  | accept (b : Bool)
  /-- About to transmit data `d` with sequence bit `b`. -/
  | transmit (b d : Bool)
  /-- Waiting for the acknowledgement of `b`, holding `d` for retransmission. -/
  | await (b d : Bool)
  deriving DecidableEq

/-- **Receiver states of the alternating-bit protocol with data.** For bits $b$ and $d$, a receiver
state is $\mathsf{expect}(b)$, expecting a frame with sequence bit $b$; $\mathsf{deliver}(b, d)$,
about to deliver the data bit $d$ of a frame with sequence bit $b$; or $\mathsf{reply}(b)$, about
to acknowledge $b$. -/
inductive Receiver
  /-- Expecting a frame with sequence bit `b`. -/
  | expect (b : Bool)
  /-- About to deliver data `d` of a frame with sequence bit `b`. -/
  | deliver (b d : Bool)
  /-- About to acknowledge `b`. -/
  | reply (b : Bool)
  deriving DecidableEq

/-- **Sender transitions of the alternating-bit protocol with data.** The transitions of each
sender state, as a list of pairs of a label and a successor state, for bits $b$ and $d$:
$\mathsf{accept}(b)$ inputs on $\mathsf{acc}(d)$ and moves to $\mathsf{transmit}(b, d)$, for
$d = \mathrm{false}$ and then $d = \mathrm{true}$; $\mathsf{transmit}(b, d)$ outputs on
$\mathsf{send}(b, d)$ and moves to $\mathsf{await}(b, d)$; and $\mathsf{await}(b, d)$ inputs on
$\mathsf{ack}(b)$ and moves to $\mathsf{accept}(\lnot b)$, inputs on $\mathsf{ack}(\lnot b)$ and
stays in $\mathsf{await}(b, d)$, or times out by a silent step $\tau$ back to
$\mathsf{transmit}(b, d)$, in this order. -/
def senderSteps : Sender → List (Label Name × Sender)
  | .accept b => [(.input (.acc false), .transmit b false), (.input (.acc true), .transmit b true)]
  | .transmit b d => [(.output (.send b d), .await b d)]
  | .await b d =>
      [(.input (.ack b), .accept (!b)), (.input (.ack (!b)), .await b d), (.tau, .transmit b d)]

/-- **Data-channel transitions of the alternating-bit protocol with data.** The data channel is a
lossy one-place channel whose content is either empty or a pair $(b, d)$ of a sequence bit $b$
and a data bit $d$. Its transitions, as a list of pairs of a label and a successor content: the
empty channel inputs on $\mathsf{send}(b, d)$ and then holds $(b, d)$, for the four pairs $(b, d)$
in the order $(\mathrm{false}, \mathrm{false})$, $(\mathrm{false}, \mathrm{true})$,
$(\mathrm{true}, \mathrm{false})$, $(\mathrm{true}, \mathrm{true})$; a channel holding $(b, d)$
either outputs on $\mathsf{recv}(b, d)$ and becomes empty, or loses the frame by a silent step
$\tau$ and becomes empty. -/
def dataSteps : Option (Bool × Bool) → List (Label Name × Option (Bool × Bool))
  | none => [false, true].flatMap fun b => [false, true].map fun d =>
      (.input (.send b d), some (b, d))
  | some (b, d) => [(.output (.recv b d), none), (.tau, none)]

/-- **Receiver transitions of the alternating-bit protocol with data.** The transitions of each
receiver state, as a list of pairs of a label and a successor state, for bits $b$ and $d$:
$\mathsf{expect}(b)$ inputs on $\mathsf{recv}(b, d)$ and moves to $\mathsf{deliver}(b, d)$, or
inputs a duplicate on $\mathsf{recv}(\lnot b, d)$ and moves to the state $\mathsf{reply}(\lnot b)$,
these two for $d = \mathrm{false}$ and then for $d = \mathrm{true}$; $\mathsf{deliver}(b, d)$
outputs on $\mathsf{del}(d)$ and moves to the state $\mathsf{reply}(b)$; and the state
$\mathsf{reply}(b)$ outputs on the channel $\mathsf{reply}(b)$ and moves to
$\mathsf{expect}(\lnot b)$. So the receiver delivers the data of an expected frame and
acknowledges a duplicate again. -/
def receiverSteps : Receiver → List (Label Name × Receiver)
  | .expect b => [false, true].flatMap fun d =>
      [(.input (.recv b d), .deliver b d), (.input (.recv (!b) d), .reply (!b))]
  | .deliver b d => [(.output (.del d), .reply b)]
  | .reply b => [(.output (.reply b), .expect (!b))]

/-- **Acknowledgement channel of the alternating-bit protocol with data.** The transitions of the
lossy one-place acknowledgement channel: when empty, it can take an input on $\mathrm{reply}_b$
for either bit $b$ and then holds $b$; when holding $b$, it can either output on $\mathrm{ack}_b$
or lose $b$ by a silent step, and in both cases it becomes empty. -/
def ackSteps : Option Bool → List (Label Name × Option Bool)
  | none => [(.input (.reply false), some false), (.input (.reply true), some true)]
  | some b => [(.output (.ack b), none), (.tau, none)]

/-- **Transitions of the one-place buffer of bits.** When empty, the buffer can take an input on
$\mathrm{acc}_d$ for either bit $d$ and then holds $d$; when holding $d$, its only transition is
an output on $\mathrm{del}_d$, after which it is empty. -/
def bufferSteps : Option Bool → List (Label Name × Option Bool)
  | none => [(.input (.acc false), some false), (.input (.acc true), some true)]
  | some d => [(.output (.del d), none)]

/-- **Process constants of the alternating-bit protocol with data.** There is one process constant
for each sender state, each content of the data channel (empty, or a sequence bit with a data
bit), each receiver state, each content of the acknowledgement channel (empty, or a bit), and each
content of the one-place buffer of bits (empty, or a bit). -/
inductive Agent
  | sender (s : Sender)
  | data (c : Option (Bool × Bool))
  | receiver (r : Receiver)
  | ack (c : Option Bool)
  | buffer (content : Option Bool)

/-- **Recursive specification of the alternating-bit protocol with data.** There is a separate
process constant $X_s$ for each state $s$ of each of five components: the sender, the lossy data
channel, the receiver, the lossy acknowledgement channel and the one-place buffer of bits. If
$(a_1, s_1), \dots, (a_n, s_n)$ are the listed transitions of $s$ in its component, then the body
of $X_s$ is the choice of prefixes $a_1.X_{s_1} + (a_2.X_{s_2} + \dots + (a_n.X_{s_n} + 0))$,
where each $X_{s_i}$ is the constant of the same component and $0$ is the inactive process; the
body is $0$ when $s$ has no listed transitions. -/
def spec : Specification Name Agent
  | .sender s => sumOf ((senderSteps s).map fun y => (y.1, .constant (.sender y.2)))
  | .data c => sumOf ((dataSteps c).map fun y => (y.1, .constant (.data y.2)))
  | .receiver r => sumOf ((receiverSteps r).map fun y => (y.1, .constant (.receiver y.2)))
  | .ack c => sumOf ((ackSteps c).map fun y => (y.1, .constant (.ack y.2)))
  | .buffer q => sumOf ((bufferSteps q).map fun y => (y.1, .constant (.buffer y.2)))

/-- **Transition system of the alternating-bit protocol with data.** The labelled transition
system whose states are the CCS processes over the protocol's channel names and process
constants, whose labels are the CCS labels over its channel names, and whose transitions are
generated by the protocol's recursive specification. -/
abbrev lts : LTS (Process Name Agent) (Label Name) := Process.lts spec

/-- **Internal channels of the alternating-bit protocol with data.** The list of the channel names
that the protocol restricts: $\mathsf{send}(b, d)$ followed by $\mathsf{recv}(b, d)$ for the pairs
$(b, d)$ in the order $(\mathrm{false}, \mathrm{false})$, $(\mathrm{false}, \mathrm{true})$,
$(\mathrm{true}, \mathrm{false})$, $(\mathrm{true}, \mathrm{true})$, then
$\mathsf{reply}(\mathrm{false})$, $\mathsf{reply}(\mathrm{true})$, $\mathsf{ack}(\mathrm{false})$
and $\mathsf{ack}(\mathrm{true})$. -/
def internal : List Name :=
  ([false, true].flatMap fun b => [false, true].flatMap fun d => [.send b d, .recv b d]) ++
    [.reply false, .reply true, .ack false, .ack true]

/-- **Configurations of the alternating-bit protocol with data.** A configuration consists of a
sender state, the content of the data channel (empty, or a pair of a sequence bit and a data
bit), a receiver state, and the content of the acknowledgement channel (empty, or a bit). -/
abbrev Config := ((Sender × Option (Bool × Bool)) × Receiver) × Option Bool

/-- **The alternating-bit protocol with data in a configuration.** For a configuration $c$ made of
a sender state $s$, a data-channel content $d$, a receiver state $r$ and an
acknowledgement-channel content $k$, the protocol process at $c$ is
$((X_s \mid X_d) \mid X_r) \mid X_k$ with every internal channel restricted, where $X_s$, $X_d$,
$X_r$ and $X_k$ are the process constants of these states. The internal channels are all channel
names other than accepting and delivering a data bit. -/
def system (c : Config) : Process Name Agent :=
  .restriction internal
    (.parallel
      (.parallel (.parallel (.constant (.sender c.1.1.1)) (.constant (.data c.1.1.2)))
        (.constant (.receiver c.1.2)))
      (.constant (.ack c.2)))

/-- **Transitions of the alternating-bit protocol with data.** For a configuration, made of a
sender state, a data-channel content, a receiver state and an acknowledgement-channel content,
the transitions are those of the parallel composition of the sender, the data channel, the
receiver and the acknowledgement channel, where one component moves alone or two components
synchronize on complementary labels in a silent step. Of these, only the silent steps and the
actions on names that are not internal channels are kept; the internal channels are the sending,
receiving, reply and acknowledgement channels. -/
def configSteps : Config → List (Label Name × Config) :=
  restrictSteps internal
    (parSteps (parSteps (parSteps senderSteps dataSteps) receiverSteps) ackSteps)

theorem realizes_system : Realizes spec system configSteps :=
  ((((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.receiver receiverSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.ack ackSteps fun _ => rfl)).restriction internal

/-- **The one-place buffer of bits with given content.** For a content $q$, which is either empty
or a bit, the process constant of the one-place buffer of bits holding $q$. -/
def buffer (q : Option Bool) : Process Name Agent := .constant (.buffer q)

theorem realizes_buffer : Realizes spec buffer bufferSteps :=
  Realizes.constant Agent.buffer bufferSteps fun _ => rfl

/-- **Initial configuration of the alternating-bit protocol with data.** The configuration in
which the sender is in state $\mathsf{accept}(\mathrm{false})$, ready to accept a message to be
sent with sequence bit false, the data channel and the acknowledgement channel are empty, and
the receiver is in state $\mathsf{expect}(\mathrm{false})$, expecting a frame with sequence bit
false. -/
def initial : Config := (((.accept false, none), .expect false), none)

/-- **The alternating-bit protocol with data.** The protocol process in its initial
configuration: the sender is ready to accept a data bit, to be sent with sequence bit false, the
data channel and the acknowledgement channel are empty, and the receiver expects a frame with
sequence bit false. The four agents run in parallel, with all internal channels restricted. -/
def abpData : Process Name Agent := system initial

/-- **The empty one-place buffer of bits.** The process constant of the one-place buffer of bits
with empty content. -/
def buf : Process Name Agent := buffer none

/-- **Weak-bisimulation certificate for the alternating-bit protocol with data.** A list of 220
pairs, each a protocol configuration together with the buffer content it simulates: every
reachable configuration with the buffer content it simulates, listed so that every pair reaches
the visible actions of its buffer state through pairs listed earlier. -/
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

/-- **The alternating-bit protocol with data is observation congruent to the buffer.** In the
labelled transition system of the protocol's recursive specification, the alternating-bit protocol
with data is observation congruent (rooted weakly bisimilar) to the empty one-place buffer of
bits: every transition of either process with some label is matched by the other process through
silent steps, then one actual step with the same label, then silent steps, and the two resulting
processes are weakly bisimilar. -/
theorem abpData_observationCongruent_buffer :
    lts.RootedWeaklyBisimilar abpData buf :=
  rootedWeaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := none) (by decide +kernel)

end Cslib.Algorithms.CCS.AlternatingBitData
