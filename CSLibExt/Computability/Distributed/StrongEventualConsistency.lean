/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Mathlib.Data.Finset.Defs

/-!
# Strong eventual consistency

We follow Shapiro, Preguiça, Baquero and Zawirski, *Conflict-free Replicated Data Types*,
Definitions 2–3 of the SSS 2011 paper and Definitions 2.2–2.3 of
[INRIA RR-7687](https://www.lip6.fr/Marc.Shapiro/papers/RR-7687.pdf).
The predicates concern one abstract history of a replicated object;
an object satisfies a predicate when each of its admissible histories does.

The report indexes each replica's causal history and state by its local method executions.
We allow independently chosen observation ticks for strong convergence, so it compares local
prefixes even when they are not observed simultaneously. For eventual convergence we make
“eventually” precise as a same-tick tail condition: if two correct replicas' delivered sets
agree at every tick from some cutoff on, their states are equivalent at every tick from some
later cutoff on. The delivered sets need not stop growing on that tail.

Snapshots use the same `ωSequence` carrier as `Cslib.LTS.OmegaExecution`: a labelled execution
can supply snapshots by projecting its states and deliveries by observing its labels. No
transition relation, failure detector, or communication mechanism is part of these predicates.
-/

@[expose] public section

namespace Cslib.Distributed.Replication

/-- Observations of one infinite history of a replicated object. Snapshot `t` is taken just
before step `t`. The caller designates which replicas count as correct in this history;
this is a run-level classification, not a momentary availability test. -/
structure History (Replica UpdateId State : Type*) where
  /-- The replicas treated as correct for this history, e.g. those that never crash. -/
  correct : Replica → Prop
  /-- The local payload of each replica at each snapshot. -/
  states : ωSequence (Replica → State)
  /-- Updates delivered in each step at each replica. An `UpdateId` identifies one occurrence,
  not its arguments: two executions of an update with equal arguments have different IDs.
  Local updates count as deliveries at their origin; repeated deliveries of an ID do not matter. -/
  deliveries : ωSequence (Replica → Finset UpdateId)
  /-- Actual method executions started at each replica, including queries, updates and internal
  methods. The replica and start step identify the execution; at most one starts there per step. -/
  started : Replica → ℕ → Prop
  /-- The completion step of the execution identified by its replica and start step, if any. -/
  completion : Replica → ℕ → Option ℕ
  /-- A recorded completion belongs to a started execution and cannot precede its start.
  Starting and finishing in the same step represents an atomic execution. -/
  completion_valid : ∀ r t u, completion r t = some u → started r t ∧ t ≤ u

variable {Replica UpdateId State : Type*}

/-- The cumulative set of update occurrences delivered to `r` strictly before snapshot `t`.
It is empty at snapshot zero, and delivering an ID again does not add a new occurrence. -/
def History.delivered (H : History Replica UpdateId State) (r : Replica) (t : ℕ) : Set UpdateId :=
  {u | ∃ k < t, u ∈ H.deliveries k r}

/-- Once delivered, an update remains in the causal history of that replica. -/
theorem History.delivered_mono (H : History Replica UpdateId State) (r : Replica)
    {t t' : ℕ} (ht : t ≤ t') : H.delivered r t ⊆ H.delivered r t' := by
  rintro u ⟨k, hk, hu⟩
  exact ⟨k, lt_of_lt_of_le hk ht, hu⟩

/-- An update already delivered to a correct replica is delivered to every correct replica
by some snapshot at or after that observation. -/
def EventualDelivery (H : History Replica UpdateId State) : Prop :=
  ∀ i j, H.correct i → H.correct j → ∀ t u, u ∈ H.delivered i t →
    ∃ t' ≥ t, u ∈ H.delivered j t'

/-- Every started method execution has a completion, with no correctness guard on the replica.
An execution without a recorded completion is pending forever in this infinite history. -/
def Termination (H : History Replica UpdateId State) : Prop :=
  ∀ r t, H.started r t → ∃ u ≥ t, H.completion r t = some u

variable (H : History Replica UpdateId State) (stateEq : Setoid State)

/-- If two correct replicas have equal cumulative delivered sets throughout a tail, then
at every tick of some later tail their states are equivalent under `stateEq` (e.g. give the
same answers to all queries). An isolated equality of delivered sets is not enough. -/
def EventualConvergence : Prop :=
  ∀ i j, H.correct i → H.correct j → ∀ t,
    (∀ k ≥ t, H.delivered i k = H.delivered j k) →
    ∃ t' ≥ t, ∀ k ≥ t', stateEq.r (H.states k i) (H.states k j)

/-- Whenever two observations at correct replicas have the same cumulative delivered set,
their states are equivalent under `stateEq` at those observations, with no further waiting.
The two ticks may differ. -/
def StrongConvergence : Prop :=
  ∀ i j, H.correct i → H.correct j → ∀ t t',
    H.delivered i t = H.delivered j t' → stateEq.r (H.states t i) (H.states t' j)

/-- Eventual consistency: eventual delivery, eventual convergence and method termination. -/
def EventualConsistency : Prop :=
  EventualDelivery H ∧ EventualConvergence H stateEq ∧ Termination H

/-- Strong eventual consistency: eventual delivery, immediate strong convergence and method
termination. Equivalently, it is eventual consistency plus strong convergence. -/
def StrongEventualConsistency : Prop :=
  EventualDelivery H ∧ StrongConvergence H stateEq ∧ Termination H

variable {H stateEq}

/-- Under strong convergence, a tail of equal delivered sets is already a tail of equivalent
states: apply strong convergence at the same tick on both sides. -/
theorem StrongConvergence.eventualConvergence (h : StrongConvergence H stateEq) :
    EventualConvergence H stateEq := by
  intro i j hi hj t hTail
  exact ⟨t, le_rfl, fun k hk => h i j hi hj k k (hTail k hk)⟩

/-- Strong eventual consistency implies eventual consistency on the same history. -/
theorem StrongEventualConsistency.eventualConsistency (h : StrongEventualConsistency H stateEq) :
    EventualConsistency H stateEq :=
  ⟨h.1, h.2.1.eventualConvergence, h.2.2⟩

/-- The three-clause formulation of strong eventual consistency agrees with adding strong
convergence to eventual consistency, as in Definition 2.3 of RR-7687. -/
theorem strongEventualConsistency_iff :
    StrongEventualConsistency H stateEq ↔
      EventualConsistency H stateEq ∧ StrongConvergence H stateEq :=
  ⟨fun h => ⟨h.eventualConsistency, h.2.1⟩, fun ⟨h, hc⟩ => ⟨h.1, hc, h.2.2⟩⟩

end Cslib.Distributed.Replication
