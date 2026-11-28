/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.ReliableBroadcast

/-!
# Causal broadcast with vector timestamps

A wrapper step is a broadcast, transport receipt, inspection of a pending-set candidate, crash,
or idle step. A broadcast tags a fresh message with the sender's vector *before* the increment
and immediately delivers the message locally. A receipt from another process adds its packet to
pending. Inspection, which may be interleaved with further inputs, removes and delivers a pending
packet exactly when the receiver's counts dominate its tag. A receipt from oneself does nothing.
All processes, including ones that later crash, follow the same rules. Time indexes a single
interleaving; it does not impose a common delivery order on different receivers.

`Legal` checks the transition guards against finite prefixes of the trace, without assuming a
sender-prefix or causal-order property. `FairInspection` asks the scheduler to revisit candidates
that remain pending at correct receivers, not to deliver them. The transport interface is the
canonical `ReliableBroadcast.IsReliableBroadcast` on stamped packets. The application interface
forgets stamps, retains sender and serial, and separates broadcast and prompt delivery by one
observable microstep.

Source: A. Bieniusa, *Programming Distributed Systems: Fault-tolerance in Message-Passing
Distributed Systems*, 2020, slides 41 and 47 (reliable causal broadcast and Algorithm 2).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.VectorTimestampBroadcast

open ReliableBroadcast

/-- Application messages carry sender, zero-based sender serial, and arbitrary data. -/
abbrev Message := Diffusion.Message

/-- A reliable-transport packet pairs an application message with a delivery-count vector. -/
abbrev Packet (P D : Type*) := Message P D × (P → ℕ)

/-- One atomic wrapper action. The Boolean records the result of inspecting a candidate;
legality checks it in both directions. -/
inductive Step (P D : Type*) where
  /-- Broadcast locally, reliably send the tagged message, and record its prompt self-delivery. -/
  | send (w : Packet P D)
  /-- A transport delivery; a non-self packet enters pending, while a self echo is ignored. -/
  | receive (p : P) (w : Packet P D)
  /-- Inspect a candidate at a receiver. A successful inspection causes one causal delivery. -/
  | inspect (p : P) (w : Packet P D) (taken : Bool)
  /-- Stop a process permanently. -/
  | crash (p : P)
  /-- Elapse one step without a process action. -/
  | idle

variable {P D : Type*}

/-- The process taking this step, absent for an idle step. -/
def Step.actor : Step P D → Option P
  | .send w => some w.1.sender
  | .receive p _ | .inspect p _ _ | .crash p => some p
  | .idle => none

/-- The lower-layer event: only sends and receipts are visible to reliable broadcast. -/
def Step.transport : Step P D → Option (Event P (Packet P D))
  | .send w => some (.broadcast w.1.sender w)
  | .receive p w => some (.deliver p w)
  | _ => none

/-- The upper-layer delivery, still paired with its tag for reasoning about the internal state. -/
def Step.output : Step P D → Option (P × Packet P D)
  | .send w => some (w.1.sender, w)
  | .inspect p w true => some (p, w)
  | _ => none

/-- The application broadcast, without the transport tag. -/
def Step.input : Step P D → Option (Event P (Message P D))
  | .send w => some (.broadcast w.1.sender w.1)
  | _ => none

/-- Counts increase in exactly the component indexed by a delivery's receiver and origin. -/
def Step.component (s : Step P D) : Option (P × P) :=
  s.output.map fun (p, w) => (p, w.1.sender)

/-- A schedule of atomic wrapper steps, including idle steps after a finite execution. -/
abbrev Trace (P D : Type*) := ℕ → Step P D

variable (a : Trace P D)

/-- The processes that never take a crash step. -/
def correct : Set P := {p | ∀ i, a i ≠ .crash p}

/-- Just before step `t`, a packet is pending if received from another process and not drained.
On an integrity-respecting transport, there is at most one such receipt at this receiver. -/
def Pending (p : P) (w : Packet P D) (t : ℕ) : Prop :=
  p ≠ w.1.sender ∧ (∃ i < t, a i = .receive p w) ∧
    ∀ i < t, (a i).output ≠ some (p, w)

/-- Fair local inspections: if a packet stays pending at a correct receiver from any given
cut onwards, the scheduler inspects that very packet there at or after that cut. No assumption
mentions its tag, whether the inspection succeeds, or a causal delivery. -/
def FairInspection : Prop :=
  ∀ p ∈ correct a, ∀ w t, (∀ u ≥ t, Pending a p w u) →
    ∃ u ≥ t, ∃ b, a u = .inspect p w b

variable [DecidableEq P]

/-- Receiver `p`'s vector component for origin `r` just before step `t`, starting at zero. -/
def clock (p r : P) : ℕ → ℕ
  | 0 => 0
  | t + 1 => clock p r t + if (a t).component = some (p, r) then 1 else 0

/-- A candidate fits if the receiver has reached all the transmitted counts. -/
def Fits (p : P) (w : Packet P D) (t : ℕ) : Prop := ∀ r, w.2 r ≤ clock a p r t

/-- The local transition guard at a cut, for the indicated step. No actor may act after a crash;
a sender chooses its next serial and snapshots its counts; inspection takes the candidate iff
it is pending and fits. A transport receipt by itself never outputs an application delivery. -/
def Admissible (t : ℕ) (s : Step P D) : Prop :=
  (∀ p, s.actor = some p → ∀ i < t, a i ≠ .crash p) ∧
  match s with
  | .send w => w.1.seq = clock a w.1.sender w.1.sender t ∧ w.2 = fun r => clock a w.1.sender r t
  | .inspect p w b => (b = true ↔ Pending a p w t ∧ Fits a p w t)
  | _ => True

/-- Every step of this trace passes the local transition guard on its own prior history. -/
def Legal : Prop := ∀ t, Admissible a t (a t)

/-- The counter equals the number of application delivery events from the indicated origin to
the indicated process in the strict prefix (independently of payload equality). -/
theorem clock_eq_count (p r : P) (t : ℕ) : clock a p r t =
    (List.range t).countP (fun i => decide ((a i).component = some (p, r))) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [clock, List.range_succ, ih]

/-- The transport hypothesis of the wrapper: validity and ordinary correct-process agreement,
with uniform integrity, on the actual send/receipt projection. -/
abbrev Transport := IsReliableBroadcast (fun w : Packet P D => w.1.sender) (correct a)
  (fun t => (a t).transport)

/-- Application observation: broadcast at even microtime `2*t`, delivery at `2*t+1`.
The send step has both observations; receiving a self echo has neither. -/
def application (n : ℕ) : Option (Event P (Message P D)) :=
  if n % 2 = 0 then (a (n / 2)).input else
    (a (n / 2)).output.map fun (p, w) => .deliver p w.1

/-- One direct dependency: before sending `y`, its sender broadcast or application-delivered
`x`. Observations are of the application, never of mere transport receipt. -/
def ObservedBefore (x y : Message P D) : Prop :=
  ∃ i j, i < j ∧ application a j = some (.broadcast y.sender y) ∧
    (application a i = some (.broadcast y.sender x) ∨ application a i = some (.deliver y.sender x))

/-- Application causality is the transitive closure of actual local observations before sends. -/
abbrev Precedes := Relation.TransGen (ObservedBefore a)

end Cslib.Distributed.VectorTimestampBroadcast
