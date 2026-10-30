/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dining philosophers: atomic acquisition and the butler
-/
module

public import CSLibExt.Algorithms.Concurrency.DiningPhilosophers

/-!
# Dining philosophers: atomic acquisition and the butler

Two more classical fixes for the naive protocol of `DiningPhilosophers.lean`,
each removing one of the conditions (Coffman, Elphick and Shoshani, *System
deadlocks*, ACM Computing Surveys 3(2), 1971) that the circular wait of the
naive protocol relies on, model checked with the same CTL model checker:

* `atomicLts`: a philosopher picks up both forks in one step, when both are
  free, so nobody holds one fork while waiting for another (no hold and wait).
* `butlerLts`: the naive protocol, but a philosopher may pick up a first fork
  only while fewer than two philosophers hold forks (a butler admits at most
  two to the table), so the three-way circular wait cannot form.

Both are deadlock free, every philosopher can always still get to eat, and
neighbours never eat together (`atomic_deadlock_free`, `atomic_can_eat`,
`atomic_mutex`, `butler_deadlock_free`, `butler_can_eat`, `butler_mutex`).
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.DiningPhilosophers

open Cslib.CTL


/-- Under atomic acquisition a thinking philosopher may start eating when both
of its forks are free; an eating philosopher may put them down. -/
def canMoveAtomic (s : State) (i : Fin 3) : Bool :=
  match (phase s i).val with
  | 0 => !held naive s i && !held naive s (i + 1)
  | 1 => false
  | _ => true

/-- The move under atomic acquisition: thinking to eating, eating to
thinking. -/
def moveAtomic (s : State) (i : Fin 3) : State :=
  setPhase s i (if (phase s i).val = 0 then 2 else 0)

/-- The transition system with atomic acquisition of both forks. -/
def atomicLts : LTS State (Fin 3) where
  Tr s i t := canMoveAtomic s i = true ∧ t = moveAtomic s i

instance (s : State) (i : Fin 3) (t : State) : Decidable (atomicLts.Tr s i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The number of philosophers holding at least one fork. -/
def seated (s : State) : ℕ :=
  ([0, 1, 2] : List (Fin 3)).countP fun i => decide (1 ≤ (phase s i).val)

/-- The naive protocol under a butler: a thinking philosopher may pick up its
first fork only while fewer than two philosophers hold forks. -/
def canMoveButler (s : State) (i : Fin 3) : Bool :=
  canMove naive s i && ((phase s i).val != 0 || decide (seated s < 2))

/-- The transition system of the naive protocol under a butler. -/
def butlerLts : LTS State (Fin 3) where
  Tr s i t := canMoveButler s i = true ∧ t = move s i

instance (s : State) (i : Fin 3) (t : State) : Decidable (butlerLts.Tr s i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Atomic acquisition prevents deadlock.** -/
theorem atomic_deadlock_free :
    Satisfies atomicLts eating initial (Formula.forallGlobally (.existsNext .top)) :=
  check_iff.mp (by decide +kernel)

/-- Under atomic acquisition each philosopher can always still get to eat. -/
theorem atomic_can_eat (i : Fin 3) :
    Satisfies atomicLts eating initial
      (Formula.forallGlobally (Formula.existsFinally (.atom i))) := by
  revert i
  decide +kernel

/-- Neighbours never eat together under atomic acquisition. -/
theorem atomic_mutex (i : Fin 3) :
    Satisfies atomicLts eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

/-- **A butler prevents deadlock.** -/
theorem butler_deadlock_free :
    Satisfies butlerLts eating initial (Formula.forallGlobally (.existsNext .top)) :=
  check_iff.mp (by decide +kernel)

/-- Under a butler each philosopher can always still get to eat. -/
theorem butler_can_eat (i : Fin 3) :
    Satisfies butlerLts eating initial
      (Formula.forallGlobally (Formula.existsFinally (.atom i))) := by
  revert i
  decide +kernel

/-- Neighbours never eat together under a butler. -/
theorem butler_mutex (i : Fin 3) :
    Satisfies butlerLts eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

end Cslib.Algorithms.Concurrency.DiningPhilosophers
