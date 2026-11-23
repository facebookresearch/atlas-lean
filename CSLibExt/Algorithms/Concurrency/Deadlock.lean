/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Deadlock and circular wait
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Set.Finite.Basic

/-!
# Deadlock and circular wait

Snapshots of resource allocation with single-instance resources (Coffman,
Elphick and Shoshani, *System deadlocks*, ACM Computing Surveys 3(2), 1971;
Holt, *Some deadlock properties of computer systems*, ACM Computing Surveys
4(3), 1972). A snapshot (`AllocState`) records the holder of each resource, if
any, and the outstanding requests; a process never requests a resource it
already holds. Mutual exclusion is built in: each resource has at most one
holder. The other conditions of Coffman et al. are assumptions of the reading,
not of the static model: requests follow the AND model (a process waits until
all its requests are granted), processes keep what they hold while waiting
(hold and wait), and nothing is taken from a holder (no preemption). Under those
assumptions a deadlocked set is a graph property of the snapshot, stated with
the wait-for relation (`WaitsFor`): `p` waits for `q` when `p` requests a
resource held by `q`. Circular wait is a cycle of `WaitsFor`.

* `Deadlocked s D`: a nonempty set of processes, each waiting for a resource
  held by a member of the set. Under the assumptions above, none of them can
  proceed and none will release what it holds.
* `exists_deadlocked_of_circularWait`: circular wait gives a deadlocked set.
* `circularWait_of_deadlocked`: with finitely many processes, a deadlocked set
  contains a cycle of the wait-for relation. So `deadlock_iff_circularWait`:
  for finitely many processes, deadlock is exactly circular wait. Finiteness is
  needed: an infinite chain of processes each waiting for the next is
  deadlocked without a cycle (see the tests).
* `not_circularWait_of_ordered`, `not_deadlocked_of_ordered`: Havender's
  resource ordering (*Avoiding deadlock in multitasking systems*, IBM Systems
  Journal 7(2), 1968). If every process requests only resources ranked above
  every resource it holds, there is no circular wait, hence, with finitely many
  processes, no deadlock.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Deadlock

variable {P Res : Type*}

/-- **Resource-allocation snapshot.** A resource-allocation snapshot, for a type $P$ of
processes and a type $R$ of resources, records for each resource the process holding it, if
any (so each resource has at most one holder), and for each process $p$ and resource $r$
whether $p$ has an outstanding request for $r$. A process never requests a resource it holds. -/
structure AllocState (P Res : Type*) where
  /-- The process holding each resource, if any. -/
  holder : Res → Option P
  /-- Outstanding requests. -/
  requests : P → Res → Prop
  /-- A process does not request a resource it holds. -/
  requests_not_held : ∀ p r, requests p r → holder r ≠ some p

namespace AllocState

variable (s : AllocState P Res)

/-- **Wait-for relation.** In a resource-allocation snapshot $s$, a process $p$ waits for a
process $q$ when there is a resource $r$ that $p$ requests in $s$ and that $q$ holds in $s$. -/
def WaitsFor (p q : P) : Prop := ∃ r, s.requests p r ∧ s.holder r = some q

/-- **Deadlocked set of processes.** In a resource-allocation snapshot $s$, a set $D$ of
processes is deadlocked when $D$ is nonempty and every process $p \in D$ waits in $s$ for some
process $q \in D$, that is, $p$ requests in $s$ a resource that $q$ holds in $s$. -/
def Deadlocked (D : Set P) : Prop := D.Nonempty ∧ ∀ p ∈ D, ∃ q ∈ D, s.WaitsFor p q

/-- **Circular wait.** A resource-allocation snapshot $s$ has circular wait when some process $p$
waits for itself through a chain of one or more wait-for edges in $s$, that is, there are
processes $p = p_0, p_1, \dots, p_k = p$ with $k \ge 1$ such that $p_{i-1}$ waits for $p_i$ in
$s$ for each $1 \le i \le k$. -/
def CircularWait : Prop := ∃ p, Relation.TransGen s.WaitsFor p p

variable {s}

/-- **No process waits for itself directly.** In a resource-allocation snapshot, no process $p$
waits for itself, that is, there is no resource that $p$ both requests and holds. -/
theorem not_waitsFor_self (p : P) : ¬ s.WaitsFor p p := fun ⟨r, hreq, hheld⟩ =>
  s.requests_not_held p r hreq hheld

/-- **A process whose requests are all free waits for no one.** In a resource-allocation
snapshot, if no resource requested by a process $p$ has a holder, then $p$ waits for no
process $q$. -/
theorem not_waitsFor_of_free {p q : P} (hfree : ∀ r, s.requests p r → s.holder r = none) :
    ¬ s.WaitsFor p q := fun ⟨r, hreq, hheld⟩ => by simp [hfree r hreq] at hheld

/-- **Circular wait yields a deadlocked set.** If a resource-allocation snapshot has
circular wait, that is, some process $p$ waits for itself through a chain of one or more
wait-for edges, then some set of processes is deadlocked.

One such set consists of the processes on a wait-for cycle through $p$. -/
theorem exists_deadlocked_of_circularWait (h : s.CircularWait) : ∃ D, s.Deadlocked D := by
  obtain ⟨p, hp⟩ := h
  refine ⟨{q | Relation.TransGen s.WaitsFor p q ∧ Relation.TransGen s.WaitsFor q p},
    ⟨p, hp, hp⟩, ?_⟩
  rintro q ⟨hpq, hqp⟩
  obtain ⟨q', hqq', hq'p⟩ := Relation.TransGen.head'_iff.mp hqp
  refine ⟨q', ⟨hpq.tail hqq', ?_⟩, hqq'⟩
  rcases Relation.ReflTransGen.cases_head hq'p with rfl | ⟨m, hm, hmp⟩
  · exact hp
  · exact Relation.TransGen.head' hm hmp

/-- **A deadlocked set forces circular wait.** In a resource-allocation snapshot with
finitely many processes, if some set of processes is deadlocked, then the snapshot has circular
wait: some process waits for itself through a chain of one or more wait-for edges.

The proof follows wait-for edges inside the deadlocked set; by finiteness it must revisit a
process. -/
theorem circularWait_of_deadlocked [Finite P] {D : Set P} (h : s.Deadlocked D) :
    s.CircularWait := by
  obtain ⟨⟨p₀, hp₀⟩, hsucc⟩ := h
  choose next hnext hwait using hsucc
  let g : D → D := fun x => ⟨next x.1 x.2, hnext x.1 x.2⟩
  let seq : ℕ → D := fun k => g^[k] ⟨p₀, hp₀⟩
  have hstep : ∀ k, s.WaitsFor (seq k).1 (seq (k + 1)).1 := fun k => by
    simp only [seq, Function.iterate_succ_apply']
    exact hwait _ _
  have hchain : ∀ i d, Relation.TransGen s.WaitsFor (seq i).1 (seq (i + d + 1)).1 := by
    intro i d
    induction d with
    | zero => exact .single (hstep i)
    | succ d ih => exact ih.tail (hstep (i + d + 1))
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite seq
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨(seq i).1, ?_⟩
    have := hchain i (j - i - 1)
    rwa [show i + (j - i - 1) + 1 = j by omega, ← heq] at this
  · refine ⟨(seq j).1, ?_⟩
    have := hchain j (i - j - 1)
    rwa [show j + (i - j - 1) + 1 = i by omega, heq] at this

/-- **Deadlock is circular wait.** In a resource-allocation snapshot with finitely many
processes, some set of processes is deadlocked if and only if the snapshot has circular wait,
that is, some process waits for itself through a chain of one or more wait-for edges. -/
theorem deadlock_iff_circularWait [Finite P] : (∃ D, s.Deadlocked D) ↔ s.CircularWait :=
  ⟨fun ⟨_, hD⟩ => circularWait_of_deadlocked hD, exists_deadlocked_of_circularWait⟩

/-! ## Resource ordering -/

/-- **Havender's resource ordering.** Let $s$ be a resource-allocation snapshot and let
$\mathrm{rank}$ assign a natural number to each resource. The snapshot $s$ is ordered by
$\mathrm{rank}$ when, for every process $p$, every resource $r$ that $p$ requests in $s$ and
every resource $r'$ that $p$ holds in $s$, we have $\mathrm{rank}(r') < \mathrm{rank}(r)$:
each process requests only resources ranked strictly above every resource it holds. -/
def Ordered (rank : Res → ℕ) : Prop :=
  ∀ p r r', s.requests p r → s.holder r' = some p → rank r' < rank r

/-- Along a wait-for chain from `p` to `q`, the resource `p` requests first and
the resource `q` holds last are linked by a chain of "held by a process that
requests" steps. -/
private theorem chain_of_transGen {p q : P} (h : Relation.TransGen s.WaitsFor p q) :
    ∃ r₁ r₂, s.requests p r₁ ∧ s.holder r₂ = some q ∧
      Relation.ReflTransGen (fun r r' => ∃ m, s.holder r = some m ∧ s.requests m r') r₁ r₂ := by
  induction h with
  | single hpq =>
      obtain ⟨r, hreq, hheld⟩ := hpq
      exact ⟨r, r, hreq, hheld, .refl⟩
  | tail _ hmq ih =>
      obtain ⟨r₁, r₂, hreq, hheld, hchain⟩ := ih
      obtain ⟨r, hreq', hheld'⟩ := hmq
      exact ⟨r₁, r, hreq, hheld', hchain.tail ⟨_, hheld, hreq'⟩⟩

/-- **Resource ordering prevents circular wait.** Let $\mathrm{rank}$ assign a natural number
to each resource. If a resource-allocation snapshot is ordered by $\mathrm{rank}$ (Havender's
discipline), that is, $\mathrm{rank}(r') < \mathrm{rank}(r)$ whenever some process requests
$r$ and holds $r'$, then the snapshot has no circular wait: no process waits for itself
through a chain of one or more wait-for edges. -/
theorem not_circularWait_of_ordered {rank : Res → ℕ} (hord : s.Ordered rank) :
    ¬ s.CircularWait := by
  rintro ⟨p, hp⟩
  obtain ⟨r₁, r₂, hreq, hheld, hchain⟩ := chain_of_transGen hp
  have hmono : ∀ a b, Relation.ReflTransGen
      (fun r r' => ∃ m, s.holder r = some m ∧ s.requests m r') a b → rank a ≤ rank b := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hstep ih =>
        obtain ⟨m, hheld', hreq'⟩ := hstep
        exact ih.trans (hord m _ _ hreq' hheld').le
  exact absurd ((hmono _ _ hchain).trans_lt (hord p r₁ r₂ hreq hheld)) (lt_irrefl _)

/-- **Resource ordering prevents deadlock.** Let $\mathrm{rank}$ assign a natural number to
each resource. If a resource-allocation snapshot with finitely many processes is ordered by
$\mathrm{rank}$ (Havender's discipline), that is, $\mathrm{rank}(r') < \mathrm{rank}(r)$
whenever some process requests $r$ and holds $r'$, then no set of processes is deadlocked. -/
theorem not_deadlocked_of_ordered [Finite P] {rank : Res → ℕ} (hord : s.Ordered rank)
    (D : Set P) : ¬ s.Deadlocked D :=
  fun hD => not_circularWait_of_ordered hord (circularWait_of_deadlocked hD)

end AllocState

end Cslib.Algorithms.Concurrency.Deadlock
