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

/-- **Alternating-bit channel names.** The channel names of the alternating-bit protocol are
$\mathit{acc}$ (accept a message from the user), $\mathit{del}$ (deliver a message to the
user), and, for each bit $b$, the internal names $\mathit{send}_b$ (sender to data channel),
$\mathit{recv}_b$ (data channel to receiver), $\mathit{reply}_b$ (receiver to acknowledgement
channel) and $\mathit{ack}_b$ (acknowledgement channel to sender). -/
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

/-- **Sender states of the data-free alternating-bit protocol.** For each bit $b$, the sender
has three states: $\mathrm{accept}(b)$, ready to accept a message to be sent with bit $b$;
$\mathrm{transmit}(b)$, about to transmit a frame tagged with bit $b$; and $\mathrm{await}(b)$,
waiting for the acknowledgement of bit $b$. These six states are all the sender states. -/
inductive Sender
  /-- Ready to accept a message, to be sent with this bit. -/
  | accept (b : Bool)
  /-- About to transmit a frame with this bit. -/
  | transmit (b : Bool)
  /-- Waiting for the acknowledgement of this bit. -/
  | await (b : Bool)
  deriving DecidableEq

/-- **States of a one-place channel.** A one-place channel is either empty or full, holding a single
bit. -/
inductive Channel
  | empty
  | full (b : Bool)
  deriving DecidableEq

/-- **Alternating-bit receiver states.** A state of the alternating-bit receiver is, for a bit
$b$, either expecting a frame with bit $b$, about to deliver the message of a frame with bit
$b$, or about to acknowledge bit $b$. -/
inductive Receiver
  /-- Expecting a frame with this bit. -/
  | expect (b : Bool)
  /-- About to deliver the message of a frame with this bit. -/
  | deliver (b : Bool)
  /-- About to acknowledge this bit. -/
  | reply (b : Bool)
  deriving DecidableEq

/-- **Alternating-bit sender transitions.** The sender of the alternating-bit protocol has the
following transitions. Ready to accept with bit $b$, it can input on $\mathit{acc}$ and become
about to transmit $b$. About to transmit $b$, it can output on $\mathit{send}_b$ and then await
the acknowledgement of $b$. Awaiting the acknowledgement of $b$, it can input on
$\mathit{ack}_b$ and become ready to accept with bit $\lnot b$, input on
$\mathit{ack}_{\lnot b}$ and keep waiting, or time out by a silent step and become about to
transmit $b$ again. -/
def senderSteps : Sender → List (Label Name × Sender)
  | .accept b => [(.input .acc, .transmit b)]
  | .transmit b => [(.output (.send b), .await b)]
  | .await b =>
      [(.input (.ack b), .accept (!b)), (.input (.ack (!b)), .await b), (.tau, .transmit b)]

/-- **Alternating-bit data channel transitions.** The one-place data channel of the
alternating-bit protocol has the following transitions. When empty, it can input on
$\mathit{send}_b$ and become full with bit $b$, for each bit $b$. When full with bit $b$, it can
output on $\mathit{recv}_b$ and become empty, or lose the bit by a silent step and become empty. -/
def dataSteps : Channel → List (Label Name × Channel)
  | .empty => [(.input (.send false), .full false), (.input (.send true), .full true)]
  | .full b => [(.output (.recv b), .empty), (.tau, .empty)]

/-- **Alternating-bit receiver transitions.** The receiver of the alternating-bit protocol has
the following transitions. Expecting bit $b$, it can input on $\mathit{recv}_b$ and become ready
to deliver $b$, or input on $\mathit{recv}_{\lnot b}$ and become ready to acknowledge $\lnot b$.
Ready to deliver $b$, it can output on $\mathit{del}$ and become ready to acknowledge $b$. Ready
to acknowledge $b$, it can output on $\mathit{reply}_b$ and then expect $\lnot b$. -/
def receiverSteps : Receiver → List (Label Name × Receiver)
  | .expect b => [(.input (.recv b), .deliver b), (.input (.recv (!b)), .reply (!b))]
  | .deliver b => [(.output .del, .reply b)]
  | .reply b => [(.output (.reply b), .expect (!b))]

/-- **Transitions of the acknowledgement channel in the data-free alternating-bit protocol.** When
empty, the lossy one-place acknowledgement channel can, for either bit $b$, input on
$\mathit{reply}_b$ and become full with bit $b$. When full with bit $b$, it can output on
$\mathit{ack}_b$ or make a silent $\tau$ step (losing the bit), in both cases becoming empty. These
are all its transitions. -/
def ackSteps : Channel → List (Label Name × Channel)
  | .empty => [(.input (.reply false), .full false), (.input (.reply true), .full true)]
  | .full b => [(.output (.ack b), .empty), (.tau, .empty)]

/-- **Transitions of the data-free one-place buffer.** The one-place buffer has two states, empty
(false) and full (true). When empty, its only transition is an input on $\mathit{acc}$ to the full
state; when full, its only transition is an output on $\mathit{del}$ to the empty state. -/
def bufferSteps : Bool → List (Label Name × Bool)
  | false => [(.input .acc, true)]
  | true => [(.output .del, false)]

/-- **Process constants of the data-free alternating-bit protocol.** There is one process constant
for each sender state, each state of the data channel, each receiver state, each state of the
acknowledgement channel, and each state of the one-place buffer (empty or full). -/
inductive Agent
  | sender (s : Sender)
  | data (c : Channel)
  | receiver (r : Receiver)
  | ack (c : Channel)
  | buffer (full : Bool)

/-- **Recursive specification of the data-free alternating-bit protocol.** The process constants
are the states of the five agents: the sender, the data channel, the receiver, the
acknowledgement channel and the one-place buffer. For a state $x$ of one of these agents, let
$(a_1, x_1), \dots, (a_n, x_n)$ be the transitions of $x$ as listed by the transition function
of its agent, let $X_i$ be the constant of the same agent at state $x_i$, and let $\mathbf{0}$
be the inactive process. The specification defines the constant of $x$ as the choice of
prefixes $a_1.X_1 + (a_2.X_2 + \cdots + (a_n.X_n + \mathbf{0}))$. -/
def spec : Specification Name Agent
  | .sender s => sumOf ((senderSteps s).map fun y => (y.1, .constant (.sender y.2)))
  | .data c => sumOf ((dataSteps c).map fun y => (y.1, .constant (.data y.2)))
  | .receiver r => sumOf ((receiverSteps r).map fun y => (y.1, .constant (.receiver y.2)))
  | .ack c => sumOf ((ackSteps c).map fun y => (y.1, .constant (.ack y.2)))
  | .buffer b => sumOf ((bufferSteps b).map fun y => (y.1, .constant (.buffer y.2)))

/-- **Alternating-bit transition system.** The labelled transition system whose states are the
CCS processes over the alternating-bit channel names and process constants, whose labels are the
CCS labels over those names, and whose transitions are the steps of the CCS operational
semantics for the recursive specification that defines each process constant (one per state of
the sender, the data channel, the receiver, the acknowledgement channel and the one-place
buffer) as the choice of its listed transitions. -/
abbrev lts : LTS (Process Name Agent) (Label Name) := Process.lts spec

/-- **Internal channels of the alternating-bit protocol.** The internal channel names, all of
which the protocol restricts, are $\mathit{send}_b$, $\mathit{recv}_b$, $\mathit{reply}_b$ and
$\mathit{ack}_b$ for both bits $b$, that is, every channel name except $\mathit{acc}$ and
$\mathit{del}$. -/
def internal : List Name :=
  [.send false, .send true, .recv false, .recv true, .reply false, .reply true,
    .ack false, .ack true]

/-- **Alternating-bit configuration.** A configuration of the alternating-bit protocol consists
of a sender state, a state of the data channel, a receiver state and a state of the
acknowledgement channel. -/
abbrev Config := ((Sender × Channel) × Receiver) × Channel

/-- **The alternating-bit protocol in a configuration.** Consider a configuration with sender
state $s$, data channel state $d$, receiver state $r$ and acknowledgement channel state $k$.
Write $\mathrm{Sender}(s)$, $\mathrm{Data}(d)$, $\mathrm{Receiver}(r)$ and $\mathrm{Ack}(k)$
for the constants of the four agents at these states, and let $L$ be the set of internal
channels $\mathrm{send}(b)$, $\mathrm{recv}(b)$, $\mathrm{reply}(b)$ and $\mathrm{ack}(b)$ for
both bits $b$. The protocol process is the parallel composition of these constants with every
internal channel restricted,
$(((\mathrm{Sender}(s) \mid \mathrm{Data}(d)) \mid \mathrm{Receiver}(r)) \mid \mathrm{Ack}(k))
\setminus L$. -/
def system (c : Config) : Process Name Agent :=
  .restriction internal
    (.parallel (.parallel (.parallel (.constant (.sender c.1.1.1)) (.constant (.data c.1.1.2)))
      (.constant (.receiver c.1.2))) (.constant (.ack c.2)))

/-- **Alternating-bit configuration transitions.** The transitions of a configuration of the
alternating-bit protocol, listed as pairs of a label and a successor configuration, are obtained
by composing the transitions of the sender, the data channel, the receiver and the
acknowledgement channel in parallel, in that order (at each stage either side moves alone, or
the two sides synchronize on an input and the complementary output on the same channel name,
giving a silent step), and then keeping only the silent steps and the steps whose channel name
is not one of the internal channel names. -/
def configSteps : Config → List (Label Name × Config) :=
  restrictSteps internal (parSteps (parSteps (parSteps senderSteps dataSteps) receiverSteps)
    ackSteps)

theorem realizes_system : Realizes spec system configSteps :=
  ((((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.receiver receiverSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.ack ackSteps fun _ => rfl)).restriction internal

/-- **The data-free one-place buffer in a given state.** For a Boolean $f$, $\mathit{buffer}(f)$ is
the process constant for the one-place buffer that is full if $f$ is true and empty if $f$ is
false. -/
def buffer (full : Bool) : Process Name Agent := .constant (.buffer full)

theorem realizes_buffer : Realizes spec buffer bufferSteps :=
  Realizes.constant Agent.buffer bufferSteps fun _ => rfl

/-- **Initial alternating-bit configuration.** The initial configuration of the alternating-bit
protocol has the sender ready to accept a message with bit $\mathrm{false}$, both channels
empty, and the receiver expecting bit $\mathrm{false}$. -/
def initial : Config := (((.accept false, .empty), .expect false), .empty)

/-- **The data-free alternating-bit protocol.** The process $\mathit{abp}$ is the protocol in its
initial configuration: the parallel composition of the sender, the lossy one-place data channel,
the receiver and the lossy one-place acknowledgement channel, with all eight internal channels
$\mathit{send}_b$, $\mathit{recv}_b$, $\mathit{reply}_b$ and $\mathit{ack}_b$ (for both bits $b$)
restricted, where the sender is ready to accept a message to be sent with bit $0$, both channels
are empty, and the receiver expects bit $0$. -/
def abp : Process Name Agent := system initial

/-- **The data-free one-place buffer.** The process $\mathit{buf}$ is the one-place buffer in its
empty state. By the specification it accepts on $\mathit{acc}$ and becomes full, and the full
buffer delivers on $\mathit{del}$ and becomes empty again, so
$\mathit{buf} = \mathit{acc}.\overline{\mathit{del}}.\mathit{buf}$. -/
def buf : Process Name Agent := buffer false

/-- **Weak-bisimulation certificate for the data-free alternating-bit protocol.** The list of every
reachable protocol configuration, paired with the buffer state it simulates (full from the accept
of a message until its delivery), sorted by silent distance to the next visible action. -/
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

/-- **The alternating-bit protocol implements a one-place buffer.** In the labelled transition
system of the protocol's recursive CCS specification, the data-free alternating-bit protocol over
lossy one-place channels is weakly bisimilar to the one-place buffer
$\mathit{buf} = \mathit{acc}.\overline{\mathit{del}}.\mathit{buf}$. -/
theorem abp_weaklyBisimilar_buffer : lts.HomWeakBisimilarity abp buf :=
  weaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := false) (by decide +kernel)

/-- **The alternating-bit protocol is observation congruent to a one-place buffer.** In the
labelled transition system of the protocol's recursive CCS specification, the data-free
alternating-bit protocol over lossy one-place channels is rooted weakly bisimilar (observation
congruent) to the one-place buffer
$\mathit{buf} = \mathit{acc}.\overline{\mathit{del}}.\mathit{buf}$.

This is stronger than weak bisimilarity; it holds because initially neither process can move
silently. -/
theorem abp_observationCongruent_buffer : lts.RootedWeaklyBisimilar abp buf :=
  rootedWeaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := false) (by decide +kernel)

end Cslib.Algorithms.CCS.AlternatingBit
