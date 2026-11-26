/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Timed message-passing runs

A run is a history (`History`) satisfying `History.WellFormed`. For `n` processors on a complete
network, each tick has a finite list of steps with no processor repeated. The external clock is
indexed by `ℕ`, starting at zero, and may have idle ticks. The order of the list linearizes
steps at the same tick: a receive may take a message sent earlier in that list, but not later.
This is a modeling convention, not a linearization result of the source paper.

A send's position identifies its occurrence, so even sends with identical endpoints and payload
are distinct. A receive selects a finite set of pending occurrences for its processor, possibly
the empty set. The local protocol sees an unordered multiset of sender–payload pairs, retaining
multiplicity but not exposing the clock or the positions used to identify occurrences. An
application may include protocol-visible tags in its payloads. Each send places its occurrence
in the buffer. Neither send omissions nor a distinction between delivery and receipt are
modeled. Decision values and their irreversibility are not modeled separately.

* `History.Conforms` checks a processor's initial state and every instruction and state change.
  An unscheduled processor keeps its state. `History.Correct` also requires unboundedly many
  ticks with steps; `History.Lost` requires an actual send and infinitely many receives by the
  intended recipient without delivery of that occurrence. Both are for infinite clock histories,
  which can have a finite number of steps. There is no separate finite-run correctness predicate.
* `History.CommunicationBound` is conditional on a send and a sufficiently late receive both
  lying in the interval. `History.ProcessorBound` tests only complete windows of the specified
  positive length and requires a step of every correct processor in each such window. Both
  predicates take a set of ticks: use an interval set for the source definition, with membership
  determining which endpoints count. They use positive parameters, as in the synchrony
  conditions in §2.3; a zero-width processor window is not part of the model.

## References

* C. Dwork, N. Lynch and L. Stockmeyer, *Consensus in the presence of partial synchrony*,
  Journal of the ACM 35(2), 1988, 288–323, §§2.1 and 2.3 (and §2.2 for processor correctness).
-/

@[expose] public section

namespace Cslib.Distributed.TimedMessagePassing

/-- A step address: tick first, then its zero-based position within that tick. The order is
lexicographic. The address of a send also names that message occurrence. -/
abbrev Position := ℕ ×ₗ ℕ

/-- The clock tick of a step address, forgetting the within-tick position. -/
def Position.tick (x : Position) : ℕ := (ofLex x).1

/-- The two deterministic instructions of a local protocol. A send fixes the recipient, payload
and successor state; a receive fixes a function from the received batch to the successor state. -/
inductive Instruction (n : ℕ) (M S : Type*) where
  | send (recipient : Fin n) (payload : M) (next : S)
  | receive (next : Multiset (Fin n × M) → S)

/-- A deterministic local protocol, with initial states determined by the input values. Both the
initialization and the choice of instruction can depend on the processor. -/
structure Protocol (n : ℕ) (V M S : Type*) where
  /-- Initialize a processor from its own input value. -/
  init : Fin n → V → S
  /-- The instruction determined by the processor and its current local state. -/
  instruction : Fin n → S → Instruction n M S

/-- The recorded action of a step: send one occurrence, or receive a set of send occurrences. -/
inductive Action (n : ℕ) (M : Type*) where
  | send (recipient : Fin n) (payload : M)
  | receive (deliveries : Finset Position)

/-- One processor step, recording its action and resulting local state. -/
structure Step (n : ℕ) (M S : Type*) where
  /-- The processor taking this step. -/
  processor : Fin n
  /-- The actual send or receive. -/
  action : Action n M
  /-- The processor's local state after this step. -/
  next : S

/-- Candidate infinite clock history for a finite complete network. The list at each tick gives
both the scheduled steps and their order. `History.WellFormed` enforces the schedule and buffer
rules independently of conformance to any particular protocol. -/
structure History (n : ℕ) (M S : Type*) where
  /-- The local states before the first tick. -/
  initial : Fin n → S
  /-- The ordered steps at each tick. Empty lists represent idle ticks. -/
  steps : ℕ → List (Step n M S)

namespace History

variable {n : ℕ} {V M S : Type*} (r : History n M S)

/-- Look up an actual step. An address beyond the end of its tick's list names no step. -/
def stepAt? (x : Position) : Option (Step n M S) := (r.steps x.tick)[(ofLex x).2]?

/-- At a send address, read the sender, recipient and payload. -/
def sendAt? (x : Position) : Option (Fin n × Fin n × M) :=
  (r.stepAt? x).bind fun s ↦ match s.action with
    | .send p m => some (s.processor, p, m)
    | .receive _ => none

/-- At a receive address, read the receiver and the batch of selected occurrences. -/
def receiveAt? (x : Position) : Option (Fin n × Finset Position) :=
  (r.stepAt? x).bind fun s ↦ match s.action with
    | .send _ _ => none
    | .receive ids => some (s.processor, ids)

/-- The receive at `x` lists the occurrence at `sent`. In a well-formed history this is an
actual delivery of that send to its intended receiver. -/
def DeliveredAt (sent x : Position) : Prop :=
  ∃ p ids, r.receiveAt? x = some (p, ids) ∧ sent ∈ ids

/-- The buffer of `p` just before position `x`: earlier sends to `p` not listed at any earlier
receive. The history starts with empty buffers; no independent buffer contents are recorded. -/
def pendingBefore (p : Fin n) (x : Position) : Set Position :=
  {sent | (∃ q m, r.sendAt? sent = some (q, p, m)) ∧ sent < x ∧
    ∀ y, y < x → ¬ r.DeliveredAt sent y}

/-- A legal run has at most one step per processor per tick, and each receive takes a subset of
its receiver's pending buffer. The receive rule excludes nonexistent, future, misaddressed and
previously delivered occurrences. It does not force a nonempty receive. -/
structure WellFormed : Prop where
  /-- Each processor takes at most one step on a given tick. -/
  oncePerTick (t : ℕ) : ((r.steps t).map Step.processor).Nodup
  /-- The occurrences consumed at a receive are pending for that receiver. -/
  receivePending (x : Position) (p : Fin n) (ids : Finset Position)
      (h : r.receiveAt? x = some (p, ids)) : (↑ids : Set Position) ⊆ r.pendingBefore p x

/-- In a legal run an occurrence cannot be delivered at two different steps. -/
theorem WellFormed.delivery_unique {r : History n M S} (h : r.WellFormed)
    {sent x y : Position} (hx : r.DeliveredAt sent x) (hy : r.DeliveredAt sent y) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · obtain ⟨p, ids, hrec, hmem⟩ := hy
    exact False.elim ((h.receivePending y p ids hrec hmem).2.2 x hlt hx)
  · exact heq
  · obtain ⟨p, ids, hrec, hmem⟩ := hx
    exact False.elim ((h.receivePending x p ids hrec hmem).2.2 y hgt hy)

/-- The protocol-visible batch for a set of occurrence addresses. Non-send addresses are
ignored; in a legal receive there are none. Several occurrences can contribute the same pair. -/
def batch (ids : Finset Position) : Multiset (Fin n × M) :=
  ids.val.filterMap fun x ↦ (r.sendAt? x).map fun (q, _, m) ↦ (q, m)

/-- The local state just before tick `t`, computed from the initial state and the recorded
successors at previous ticks. A tick with no step by `p` does not change its state. On a legal
history there is at most one step by `p` per tick, so this is also its state before that step. -/
def stateBefore (p : Fin n) : ℕ → S
  | 0 => r.initial p
  | t + 1 => match (r.steps t).find? (fun s ↦ decide (s.processor = p)) with
    | none => stateBefore p t
    | some s => s.next

/-- Local conformance checks the recorded initial state and every step of `p` against the
instruction from its actual prior state. At a receive, the successor is computed from the batch
listed at that step. The legality of the schedule and deliveries is checked by `WellFormed`. -/
def Conforms (a : Protocol n V M S) (input : Fin n → V) (p : Fin n) : Prop :=
  r.initial p = a.init p (input p) ∧
    ∀ x s, r.stepAt? x = some s → s.processor = p →
      match a.instruction p (r.stateBefore p x.tick), s.action with
      | .send q m next, .send q' m' => q = q' ∧ m = m' ∧ s.next = next
      | .receive next, .receive ids => s.next = next (r.batch ids)
      | _, _ => False

/-- Processor `p` takes a step at tick `t`. -/
def StepsAt (p : Fin n) (t : ℕ) : Prop := ∃ s ∈ r.steps t, s.processor = p

/-- A correct processor in an infinite clock history conforms and takes steps at arbitrarily
late ticks. Since each tick is finite, this means infinitely many steps. -/
def Correct (a : Protocol n V M S) (input : Fin n → V) (p : Fin n) : Prop :=
  r.Conforms a input p ∧ ∀ t, ∃ u ≥ t, r.StepsAt p u

/-- An actual send occurrence is lost if its intended receiver performs receives at arbitrarily
late ticks but the occurrence is never delivered. Merely being undelivered is insufficient. -/
def Lost (sent : Position) : Prop :=
  ∃ q p m, r.sendAt? sent = some (q, p, m) ∧
    (∀ t : ℕ, ∃ x ids, t ≤ x.tick ∧ r.receiveAt? x = some (p, ids)) ∧
    ∀ x, ¬ r.DeliveredAt sent x

/-- The positive communication bound `Δ` holds on the ticks in `I` when, for every send and
receive by its intended recipient both in `I` with `sent.tick + Δ ≤ x.tick`, the occurrence is
delivered at `x.tick` or earlier. The threshold is inclusive; actual ordering and recipient
legality are supplied by `WellFormed`. Interval endpoints count exactly when they belong to `I`.
There is no delivery deadline in the absence of a qualifying receive, nor an obligation from a
send outside `I`. -/
def CommunicationBound (I : Set ℕ) (Δ : ℕ) : Prop :=
  0 < Δ ∧ ∀ sent x q p m ids,
    r.sendAt? sent = some (q, p, m) → r.receiveAt? x = some (p, ids) →
    sent.tick ∈ I → x.tick ∈ I → sent.tick + Δ ≤ x.tick →
    ∃ y, y.tick ≤ x.tick ∧ r.DeliveredAt sent y

/-- The positive processor bound `Φ` holds on `I` if every full window `[t, t + Φ)` of `Φ`
consecutive ticks contained in `I` contains a step by every correct processor. In particular the
first tick is included and `t + Φ` is excluded. This imposes no scheduling condition if there
is no full window or no correct processor. The positive width excludes a zero-length window. -/
def ProcessorBound (a : Protocol n V M S) (input : Fin n → V) (I : Set ℕ) (Φ : ℕ) : Prop :=
  0 < Φ ∧ ∀ t, Set.Ico t (t + Φ) ⊆ I → ∀ p, r.Correct a input p →
    ∃ u ∈ Set.Ico t (t + Φ), r.StepsAt p u

end History
end Cslib.Distributed.TimedMessagePassing

end
