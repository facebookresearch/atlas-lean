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

/-- **Channel names of go-back-N.** The channel names of the go-back-N protocol are
$\mathsf{acc}$ (accept a message from the user), $\mathsf{del}$ (deliver a message to the user)
and, for every natural number $k$: $\mathsf{send}\,k$ (sender to data channel, a frame with
sequence number $k$), $\mathsf{recv}\,k$ (data channel to receiver), $\mathsf{ack}\,k$ (receiver
to sender, the cumulative acknowledgement naming $k$ as the next expected frame) and
$\mathsf{reply}\,k$ (receiver to the acknowledgement channel, in the lossy variant).

The protocol only uses the sequence numbers $0$, $1$ and $2$. -/
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

/-- **Go-back-N sender state.** A state of the go-back-N sender is a triple of natural numbers:
the base of the window (the sequence number of the oldest unacknowledged frame), the number of
outstanding messages (accepted but not yet acknowledged), and the offset from the base of the
next frame to transmit. -/
structure Sender where
  /-- The sequence number of the oldest unacknowledged frame. -/
  base : ℕ
  /-- The number of outstanding (accepted, unacknowledged) messages. -/
  out : ℕ
  /-- The offset from `base` of the next frame to transmit. -/
  next : ℕ
  deriving DecidableEq

/-- **Receiver states of go-back-N.** A receiver state is one of the following, for a natural
number $e$ or $k$: expecting the frame with sequence number $e$; about to deliver $e$, having
received the expected frame $e$; or about to acknowledge $k$, the next expected sequence
number. -/
inductive Receiver
  /-- Expecting this sequence number. -/
  | expect (e : ℕ)
  /-- Received the expected frame `e`; about to deliver it. -/
  | deliver (e : ℕ)
  /-- About to acknowledge: the next expected sequence number. -/
  | reply (k : ℕ)
  deriving DecidableEq

/-- **Sender update on an acknowledgement.** For a go-back-N sender with window base $b$, $c$
outstanding messages and next-frame offset $o$, and an acknowledgement $k$, let
$d = \max(k + 3 - b, 0) \bmod 3$. If $1 \le d \le c$, the window slides: the new sender has
base $k$, $c - d$ outstanding messages and next-frame offset $\max(o - d, 0)$. Otherwise the
sender is unchanged. -/
def ackUpdate (s : Sender) (k : ℕ) : Sender :=
  if 1 ≤ (k + 3 - s.base) % 3 ∧ (k + 3 - s.base) % 3 ≤ s.out then
    ⟨k, s.out - (k + 3 - s.base) % 3, s.next - (k + 3 - s.base) % 3⟩
  else s

/-- **Sender transitions of go-back-N.** The transitions of a sender with window base $b$, $n$
outstanding messages and next offset $o$, as pairs of a label and a successor state, in this
order: if $n < 2$, an input on $\mathsf{acc}$ to $(b, n + 1, o)$; if $o < n$, an output on
$\mathsf{send}\,((b + o) \bmod 3)$ to $(b, n, o + 1)$; if $0 < n$, a silent timeout step to
$(b, n, 0)$; and, for each $k = 0, 1, 2$, an input on $\mathsf{ack}\,k$ to the state given by
the window update of the sender for acknowledgement $k$. -/
def senderSteps (s : Sender) : List (Label Name × Sender) :=
  (if s.out < 2 then [(.input .acc, ⟨s.base, s.out + 1, s.next⟩)] else []) ++
  (if s.next < s.out then
    [(.output (.send ((s.base + s.next) % 3)), ⟨s.base, s.out, s.next + 1⟩)] else []) ++
  (if 0 < s.out then [(.tau, ⟨s.base, s.out, 0⟩)] else []) ++
  [0, 1, 2].map fun k => (.input (.ack k), ackUpdate s k)

/-- **Transitions of the go-back-N data channel.** The data channel holds at most one frame.
When empty, for each sequence number $k \in \{0, 1, 2\}$ it can input on channel
$\mathrm{send}_k$ and then hold frame $k$. When holding frame $k$, it can either output on
channel $\mathrm{recv}_k$ or silently lose the frame by a $\tau$ step; in both cases it becomes
empty. -/
def dataSteps : Option ℕ → List (Label Name × Option ℕ)
  | none => [0, 1, 2].map fun k => (.input (.send k), some k)
  | some k => [(.output (.recv k), none), (.tau, none)]

/-- **Receiver transitions of go-back-N.** The transitions of the receiver, as pairs of a label
and a successor state. Expecting $e$, for each $k = 0, 1, 2$ it can input on $\mathsf{recv}\,k$
and then is about to deliver $e$ if $k = e$, and about to acknowledge $e$ otherwise. About to
deliver $e$, it outputs on $\mathsf{del}$ and is then about to acknowledge $(e + 1) \bmod 3$.
About to acknowledge $k$, it outputs on $\mathsf{ack}\,k$ and then expects $k$. -/
def receiverSteps : Receiver → List (Label Name × Receiver)
  | .expect e => [0, 1, 2].map fun k =>
      (.input (.recv k), if k = e then .deliver e else .reply e)
  | .deliver e => [(.output .del, .reply ((e + 1) % 3))]
  | .reply k => [(.output (.ack k), .expect k)]

/-- **Transitions of the two-place buffer.** The transitions of the go-back-N two-place buffer
at occupancy $n \in \mathbb{N}$: if $n < 2$ it inputs on $\mathsf{acc}$ and moves to occupancy
$n + 1$, and if $n > 0$ it outputs on $\mathsf{del}$ and moves to occupancy $n - 1$. It has no
other transitions. -/
def bufferSteps (n : ℕ) : List (Label Name × ℕ) :=
  (if n < 2 then [(.input .acc, n + 1)] else []) ++
  (if 0 < n then [(.output .del, n - 1)] else [])

/-- **Transitions of the lossy acknowledgement channel.** The lossy one-place acknowledgement
channel of the lossy go-back-N variant, given by its transitions in each state. When empty, it
inputs on $\mathsf{reply}_k$ and then holds $k$, for each $k \in \{0, 1, 2\}$. When it holds
$k$, it either outputs on $\mathsf{ack}_k$ or silently loses $k$, and in both cases it becomes
empty. It has no other transitions. -/
def ackChannelSteps : Option ℕ → List (Label Name × Option ℕ)
  | none => [0, 1, 2].map fun k => (.input (.reply k), some k)
  | some k => [(.output (.ack k), none), (.tau, none)]

/-- **Receiver transitions of lossy go-back-N.** The transitions of the receiver of the lossy
variant, as pairs of a label and a successor state, are those of the receiver of the reliable
protocol, except in the state about to acknowledge $k$: there the only transition is an output on
$\mathsf{reply}\,k$, to the acknowledgement channel, after which the receiver expects $k$. -/
def lossyReceiverSteps : Receiver → List (Label Name × Receiver)
  | .reply k => [(.output (.reply k), .expect k)]
  | r => receiverSteps r

/-- **Process constants of the go-back-N model.** The process constants of the go-back-N
specification, one for each state of each component: a sender constant for each sender state, a
data-channel constant for each channel content (empty or a natural number), a receiver constant
for each receiver state, a buffer constant for each occupancy $n \in \mathbb{N}$, an
acknowledgement-channel constant for each channel content (empty or a natural number), and a
constant for each receiver state of the lossy variant. -/
inductive Agent
  | sender (s : Sender)
  | data (k : Option ℕ)
  | receiver (r : Receiver)
  | buffer (n : ℕ)
  | ackChannel (k : Option ℕ)
  | lossyReceiver (r : Receiver)

/-- **Recursive CCS specification of go-back-N.** The specification assigns to every process
constant the choice, over the transitions listed for its state, of the prefixes $a.K$, where $a$
is the label of the transition and $K$ is the process constant for its target state; an empty
list gives the inactive process. The constants are those of the sender, the data channel, the
receiver, the two-place buffer, the acknowledgement channel and the receiver of the lossy
variant, and their transitions are the sender steps, data channel steps, receiver steps, buffer
steps, acknowledgement channel steps and lossy receiver steps respectively. -/
def spec : Specification Name Agent
  | .sender s => sumOf ((senderSteps s).map fun y => (y.1, .constant (.sender y.2)))
  | .data k => sumOf ((dataSteps k).map fun y => (y.1, .constant (.data y.2)))
  | .receiver r => sumOf ((receiverSteps r).map fun y => (y.1, .constant (.receiver y.2)))
  | .buffer n => sumOf ((bufferSteps n).map fun y => (y.1, .constant (.buffer y.2)))
  | .ackChannel k => sumOf ((ackChannelSteps k).map fun y => (y.1, .constant (.ackChannel y.2)))
  | .lossyReceiver r =>
      sumOf ((lossyReceiverSteps r).map fun y => (y.1, .constant (.lossyReceiver y.2)))

/-- **Labelled transition system of go-back-N.** The labelled transition system whose states are
the CCS processes over the go-back-N channel names and process constants, whose labels are the
CCS labels over the channel names, and whose transitions are those generated by the go-back-N
recursive specification. -/
abbrev lts : LTS (Process Name Agent) (Label Name) := Process.lts spec

/-- **Internal channels of go-back-N.** The internal channels of the go-back-N protocol are
$\mathrm{send}_k$ (sender to data channel), $\mathrm{recv}_k$ (data channel to receiver) and
$\mathrm{ack}_k$ (receiver to sender) for $k \in \{0, 1, 2\}$; all of them are restricted. -/
def internal : List Name :=
  [.send 0, .send 1, .send 2, .recv 0, .recv 1, .recv 2, .ack 0, .ack 1, .ack 2]

/-- **Go-back-N configurations.** A configuration of the go-back-N protocol consists of a
sender state, the content of the data channel (either empty or a single frame with sequence
number $k \in \mathbb{N}$), and a receiver state. -/
abbrev Config := (Sender × Option ℕ) × Receiver

/-- **Go-back-N protocol process in a configuration.** For a configuration consisting of a sender
state $s$, a data channel content $d$ (empty or one frame) and a receiver state $r$, the protocol
process is the parallel composition $(S_s \mid D_d) \mid R_r$ of the process constants for the
sender in state $s$, the data channel holding $d$ and the receiver in state $r$, with the internal
channels restricted: the send, receive and acknowledgement channels for the sequence numbers $0$,
$1$ and $2$. -/
def system (c : Config) : Process Name Agent :=
  .restriction internal
    (.parallel (.parallel (.constant (.sender c.1.1)) (.constant (.data c.1.2)))
      (.constant (.receiver c.2)))

/-- **Transitions of go-back-N configurations.** The transitions of a go-back-N configuration
(sender, data channel, receiver) are those of the parallel composition of the three components,
in which one component moves alone or two components synchronize on complementary labels in a
silent step, restricted to the silent steps and the steps whose label is not on an internal
channel ($\mathsf{send}_k$, $\mathsf{recv}_k$ or $\mathsf{ack}_k$ for $k \in \{0, 1, 2\}$). -/
def configSteps : Config → List (Label Name × Config) :=
  restrictSteps internal (parSteps (parSteps senderSteps dataSteps) receiverSteps)

theorem realizes_system : Realizes spec system configSteps :=
  (((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.receiver receiverSteps fun _ => rfl)).restriction internal

/-- **The two-place buffer process.** For an occupancy $n \in \mathbb{N}$, the process constant
of the go-back-N specification for the two-place buffer holding $n$ messages. -/
def buffer (n : ℕ) : Process Name Agent := .constant (.buffer n)

theorem realizes_buffer : Realizes spec buffer bufferSteps :=
  Realizes.constant Agent.buffer bufferSteps fun _ => rfl

/-- **Initial configuration of go-back-N.** The initial configuration of the go-back-N
protocol consists of the sender with window base $0$, no outstanding messages and next-frame
offset $0$; the empty data channel; and the receiver expecting sequence number $0$. -/
def initial : Config := ((⟨0, 0, 0⟩, none), .expect 0)

/-- **The go-back-N protocol.** The go-back-N protocol with window size $2$ and sequence
numbers modulo $3$ is the recursive CCS process in its initial configuration: the parallel
composition of the sender with an empty window based at $0$, the empty lossy one-place data
channel, and the receiver expecting $0$, with the internal channels $\mathrm{send}_k$,
$\mathrm{recv}_k$ and $\mathrm{ack}_k$ for $k \in \{0, 1, 2\}$ restricted. -/
def goBackN : Process Name Agent := system initial

/-- **The empty two-place buffer.** The two-place buffer process of the go-back-N model with
occupancy $0$. -/
def buf : Process Name Agent := buffer 0

/-- **Weak-bisimulation certificate for go-back-N.** A list of $147$ pairs, each a go-back-N
configuration together with the occupancy of the two-place buffer it simulates, namely the number
of accepted but undelivered messages. It contains every reachable configuration, and it is
ordered so that every pair can reach the visible actions of its buffer state through pairs listed
earlier. -/
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

/-- **Go-back-N with window 2 is observation congruent to a two-place buffer.** The
go-back-N protocol is observation congruent (rooted weakly bisimilar) to the empty two-place
buffer: every transition of either process is matched by a rooted weak transition of the
other with the same label (silent steps, a step with that label, silent steps), and the
resulting processes are weakly bisimilar. -/
theorem goBackN_observationCongruent_buffer :
    lts.RootedWeaklyBisimilar goBackN buf :=
  rootedWeaklyBisimilar_of_certCheck realizes_system realizes_buffer certCheck_certificate
    (x := initial) (y := 0) (by decide +kernel)

/-! ## Lossy acknowledgements -/

/-- **Internal channels of lossy go-back-N.** The list of channels restricted in the lossy
variant: the internal channels of the reliable protocol, namely $\mathsf{send}\,k$,
$\mathsf{recv}\,k$ and $\mathsf{ack}\,k$ for $k = 0, 1, 2$, followed by the channels
$\mathsf{reply}\,0$, $\mathsf{reply}\,1$ and $\mathsf{reply}\,2$ from the receiver to the
acknowledgement channel. -/
def lossyInternal : List Name := internal ++ [.reply 0, .reply 1, .reply 2]

/-- **Configurations of lossy go-back-N.** A configuration of the lossy go-back-N variant is a
go-back-N configuration (sender state, data channel content, receiver state) together with the
content of the acknowledgement channel, either empty or a single acknowledgement
$k \in \mathbb{N}$. -/
abbrev LossyConfig := Config × Option ℕ

/-- **The lossy go-back-N process in a configuration.** Let $c$ be a configuration of the lossy
variant, and let $S$, $D$, $R$ and $A$ be the process constants for its sender state, its
data-channel content, its receiver state (as a receiver of the lossy variant) and its
acknowledgement-channel content. The process of the lossy variant in $c$ is
$((S \mid D) \mid R) \mid A$ with the internal channels of the lossy variant restricted. -/
def lossySystem (c : LossyConfig) : Process Name Agent :=
  .restriction lossyInternal
    (.parallel
      (.parallel (.parallel (.constant (.sender c.1.1.1)) (.constant (.data c.1.1.2)))
        (.constant (.lossyReceiver c.1.2)))
      (.constant (.ackChannel c.2)))

/-- **Transitions of lossy go-back-N configurations.** The transitions of a configuration of
the lossy go-back-N variant come from the parallel composition of the sender, the data
channel, the lossy-variant receiver and the acknowledgement channel (in each composition
either side moves alone, or the two sides synchronize on complementary input and output
labels in a silent step), keeping only the silent transitions and those whose label is not
on an internal channel $\mathrm{send}_k$, $\mathrm{recv}_k$, $\mathrm{ack}_k$ or
$\mathrm{reply}_k$, $k \in \{0, 1, 2\}$. -/
def lossyConfigSteps : LossyConfig → List (Label Name × LossyConfig) :=
  restrictSteps lossyInternal
    (parSteps (parSteps (parSteps senderSteps dataSteps) lossyReceiverSteps) ackChannelSteps)

theorem realizes_lossySystem : Realizes spec lossySystem lossyConfigSteps :=
  ((((Realizes.constant Agent.sender senderSteps fun _ => rfl).parallel
    (Realizes.constant Agent.data dataSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.lossyReceiver lossyReceiverSteps fun _ => rfl)).parallel
    (Realizes.constant Agent.ackChannel ackChannelSteps fun _ => rfl)).restriction lossyInternal

/-- **Go-back-N with a lossy acknowledgement channel.** The process of the lossy variant of
go-back-N in its initial configuration: the sender's window is based at $0$ with no outstanding
messages and next offset $0$, the data channel and the acknowledgement channel are empty, and
the receiver expects frame $0$. -/
def lossyGoBackN : Process Name Agent := lossySystem (initial, none)

/-- **Configuration transitions are process transitions in lossy go-back-N.** Let $c$ and $c'$
be configurations of the lossy variant and $a$ a label. If $(a, c')$ is one of the
configuration-level transitions of $c$, then in the labelled transition system of the go-back-N
specification the lossy process in configuration $c$ has a transition labelled $a$ to the lossy
process in configuration $c'$. -/
theorem lossy_step {c c' : LossyConfig} {a : Label Name} (h : (a, c') ∈ lossyConfigSteps c) :
    lts.Tr (lossySystem c) a (lossySystem c') :=
  (realizes_lossySystem c a _).2 ⟨c', h, rfl⟩

/-- **The silent closure of the buffer is trivial.** For every occupancy $n$, every process
reachable from the go-back-N buffer with occupancy $n$ by zero or more silent steps is that
buffer itself. -/
theorem buffer_silentClosure {n : ℕ} {Q : Process Name Agent}
    (h : lts.τSTr (buffer n) Q) : Q = buffer n := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      obtain ⟨m, hm, -⟩ := (realizes_buffer n _ _).1 hstep
      simp only [bufferSteps, List.mem_append] at hm
      split_ifs at hm <;> simp_all

/-- **Visible weak steps of the buffer.** For every occupancy $n$ and every visible label $a$, if
the go-back-N buffer with occupancy $n$ reaches a process $Q$ by a weak transition labelled $a$
(silent steps, one $a$-step, silent steps), then $Q$ is the buffer with some occupancy $m$ such
that the buffer at occupancy $n$ has a transition labelled $a$ to occupancy $m$. -/
theorem buffer_weakStep {n : ℕ} {a : Label Name} {Q : Process Name Agent} (ha : a ≠ .tau)
    (h : lts.STr (buffer n) a Q) :
    ∃ m, (a, m) ∈ bufferSteps n ∧ Q = buffer m := by
  obtain ⟨before, after, hpre, hstep, hpost⟩ := (STr.iff_exists_of_ne ha).1 h
  rw [buffer_silentClosure hpre] at hstep
  obtain ⟨m, hm, rfl⟩ := (realizes_buffer n _ _).1 hstep
  exact ⟨m, hm, buffer_silentClosure hpost⟩

/-- **Silent closure of the stuck lossy go-back-N configuration.** The list of the seven
configurations of go-back-N with a lossy acknowledgement channel in which the sender's window has
base $0$ with two outstanding messages, the receiver holds frame $1$ about to deliver it, and the
acknowledgement channel is empty, while the sender's offset of the next frame to transmit and the
data channel are, in order: offset $2$ and empty, offset $0$ and empty, offset $1$ holding frame
$0$, offset $0$ holding frame $0$, offset $1$ and empty, offset $2$ holding frame $1$, and offset
$0$ holding frame $1$.

The first is the stuck configuration, reached after the acknowledgement of frame $0$ was lost; the
list is closed under silent steps (proved separately), so it contains every configuration
silently reachable from it. -/
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

/-- **The stuck lossy go-back-N configuration refuses new messages.** Consider go-back-N with a
lossy acknowledgement channel in the configuration where the sender's window has base $0$ with two
outstanding messages, both transmitted (offset of the next frame $2$), the data channel and the
acknowledgement channel are empty, and the receiver holds frame $1$ about to deliver it. This
process has no weak transition labelled by accepting a message: no sequence of silent steps
followed by an accept input and further silent steps is possible from it. -/
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
