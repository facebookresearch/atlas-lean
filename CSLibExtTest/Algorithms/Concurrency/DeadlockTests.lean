/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.Deadlock

/-!
# Tests for deadlock and circular wait

* The dining philosophers with every philosopher holding their left fork and
  requesting their right fork: circular wait, hence deadlock.
* The same table with one philosopher reaching for the lower-numbered fork
  first obeys a resource ordering: no circular wait and no deadlock.
* Finiteness is needed for "deadlock implies circular wait": with infinitely
  many processes, each waiting for the next, the whole set is deadlocked but
  there is no cycle (even though the resource ordering holds).
* A request for a free resource creates no wait-for edge, and no process waits
  for itself.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Deadlock.Tests

open AllocState

/-- Three philosophers; philosopher `i` holds fork `i` and requests fork
`i + 1`. -/
def diners : AllocState (Fin 3) (Fin 3) where
  holder f := some f
  requests p f := f = p + 1
  requests_not_held p r h := by subst h; revert p; decide

example : diners.CircularWait :=
  ⟨0, .tail (.tail (.single ⟨1, rfl, rfl⟩) ⟨2, rfl, rfl⟩) ⟨0, rfl, rfl⟩⟩

example : ∃ D, diners.Deadlocked D := deadlock_iff_circularWait.mpr
  ⟨0, .tail (.tail (.single ⟨1, rfl, rfl⟩) ⟨2, rfl, rfl⟩) ⟨0, rfl, rfl⟩⟩

/-- The asymmetric table: philosophers `0` and `1` hold their left fork and
request their right one; philosopher `2` waits for fork `0` while holding
nothing. Every request is for a fork ranked above everything the requester
holds. -/
def orderedDiners : AllocState (Fin 3) (Fin 3) where
  holder f := if f = 2 then none else some f
  requests p f := (p = 0 ∧ f = 1) ∨ (p = 1 ∧ f = 2) ∨ (p = 2 ∧ f = 0)
  requests_not_held := by decide

theorem orderedDiners_ordered : orderedDiners.Ordered (fun f => f.val) := by
  unfold Ordered
  simp only [orderedDiners]
  decide

example : ¬ orderedDiners.CircularWait := not_circularWait_of_ordered orderedDiners_ordered

example (D : Set (Fin 3)) : ¬ orderedDiners.Deadlocked D :=
  not_deadlocked_of_ordered orderedDiners_ordered D

/-- Infinitely many processes: `n` holds resource `n` and requests resource
`n + 1`. -/
def chain : AllocState ℕ ℕ where
  holder r := some r
  requests p r := r = p + 1
  requests_not_held p r h := by simp [h]

/-- The whole set is deadlocked. -/
example : chain.Deadlocked Set.univ :=
  ⟨⟨0, trivial⟩, fun p _ => ⟨p + 1, trivial, p + 1, rfl, rfl⟩⟩

/-- ... but there is no circular wait: wait-for edges strictly increase. -/
example : ¬ chain.CircularWait := not_circularWait_of_ordered (rank := id) <| by
  intro p r r' hreq hheld
  simp only [chain, Option.some.injEq] at hreq hheld
  simp only [id]
  omega

/-- At the ordered table, philosopher `1` requests only the free fork `2`, so
it waits for nobody. -/
example (q : Fin 3) : ¬ orderedDiners.WaitsFor 1 q :=
  not_waitsFor_of_free <| by
    simp only [orderedDiners]
    decide

/-- No process waits for itself. -/
example (p : Fin 3) : ¬ diners.WaitsFor p p := not_waitsFor_self p

end Cslib.Algorithms.Concurrency.Deadlock.Tests
