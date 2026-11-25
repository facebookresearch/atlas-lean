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


/-- **Enabled moves under atomic acquisition.** Philosopher $i$ can move in state $s$ when it
thinks and neither of its forks $i$ and $i + 1$ (modulo $3$) is held in $s$, or when it eats
(it then puts both forks down); a philosopher holding only its first fork cannot move. A fork
is held as in the naive protocol: philosopher $j$ holds fork $j$ when it holds its first fork
or eats, and holds fork $j + 1$ when it eats. -/
def canMoveAtomic (s : State) (i : Fin 3) : Bool :=
  match (phase s i).val with
  | 0 => !held naive s i && !held naive s (i + 1)
  | 1 => false
  | _ => true

/-- **Move of a philosopher under atomic acquisition.** In a state $s$ (the phases of the three
philosophers), the move of philosopher $i$ changes only the phase of $i$: if $i$ is thinking, it
starts eating, picking up both forks at once; otherwise it goes back to thinking. The phases of
the other two philosophers are unchanged. -/
def moveAtomic (s : State) (i : Fin 3) : State :=
  setPhase s i (if (phase s i).val = 0 then 2 else 0)

/-- **Dining philosophers with atomic fork acquisition.** The labelled transition system on the
states of the three philosophers, labelled by the philosopher that moves: there is a step
labelled $i$ from $s$ to $t$ exactly when either philosopher $i$ thinks in $s$, neither of its
forks $i$ and $i + 1$ (modulo $3$) is held in $s$, and $t$ is $s$ with philosopher $i$ eating;
or philosopher $i$ eats in $s$ and $t$ is $s$ with philosopher $i$ thinking. A fork is held as
in the naive protocol: philosopher $j$ holds fork $j$ when it holds its first fork or eats, and
holds fork $j + 1$ when it eats. -/
def atomicLts : LTS State (Fin 3) where
  Tr s i t := canMoveAtomic s i = true ∧ t = moveAtomic s i

instance (s : State) (i : Fin 3) (t : State) : Decidable (atomicLts.Tr s i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Number of seated philosophers.** The number of seated philosophers in a state $s$ is the
number of philosophers that hold at least one fork in $s$, that is, whose phase is either holding
the first fork or eating. -/
def seated (s : State) : ℕ :=
  ([0, 1, 2] : List (Fin 3)).countP fun i => decide (1 ≤ (phase s i).val)

/-- **Enabled moves under a butler.** Philosopher $i$ can move in state $s$ when it can move in
$s$ under the naive protocol and, if it is thinking, fewer than two philosophers hold at least
one fork in $s$. Under the naive protocol each philosopher $i$ picks up the left fork $i$ first
and then the right fork $i + 1$ (modulo $3$), each only when no philosopher holds it, and an
eating philosopher can always put both forks down. -/
def canMoveButler (s : State) (i : Fin 3) : Bool :=
  canMove naive s i && ((phase s i).val != 0 || decide (seated s < 2))

/-- **Dining philosophers with a butler.** The labelled transition system on the states of the
three philosophers, labelled by the philosopher that moves: there is a step labelled $i$ from
$s$ to $t$ exactly when philosopher $i$ can move in $s$ under the naive protocol, if
philosopher $i$ is thinking then fewer than two philosophers hold a fork in $s$, and $t$ is $s$
with philosopher $i$ advanced one phase (thinking to holding its first fork, to eating, to
thinking). Under the naive protocol each philosopher $i$ picks up the left fork $i$ first and
then the right fork $i + 1$ (modulo $3$), each only when no philosopher holds it, and an eating
philosopher can always put both forks down. -/
def butlerLts : LTS State (Fin 3) where
  Tr s i t := canMoveButler s i = true ∧ t = move s i

instance (s : State) (i : Fin 3) (t : State) : Decidable (butlerLts.Tr s i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Atomic acquisition prevents deadlock.** In the dining philosophers transition system with
atomic acquisition of both forks, every state reachable from the initial state (all three
philosophers thinking) has a successor: some philosopher can move. -/
theorem atomic_deadlock_free :
    Satisfies atomicLts eating initial (Formula.forallGlobally (.existsNext .top)) :=
  check_iff.mp (by decide +kernel)

/-- **Under atomic acquisition every philosopher can always still eat.** In the dining
philosophers transition system with atomic acquisition of both forks, for each philosopher
$i \in \{0, 1, 2\}$, from every state reachable from the initial state (all three philosophers
thinking) a state in which philosopher $i$ eats is reachable, in zero or more steps. -/
theorem atomic_can_eat (i : Fin 3) :
    Satisfies atomicLts eating initial
      (Formula.forallGlobally (Formula.existsFinally (.atom i))) := by
  revert i
  decide +kernel

/-- **Mutual exclusion under atomic acquisition.** In the dining philosophers transition system
with atomic acquisition of both forks, for each philosopher $i \in \{0, 1, 2\}$, in no state
reachable from the initial state (all three philosophers thinking) do philosopher $i$ and its
neighbour $i + 1$ (modulo $3$) both eat. -/
theorem atomic_mutex (i : Fin 3) :
    Satisfies atomicLts eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

/-- **A butler prevents deadlock.** In the dining philosophers transition system of the naive
protocol under a butler, every state reachable from the initial state (all three philosophers
thinking) has a successor: some philosopher can move. -/
theorem butler_deadlock_free :
    Satisfies butlerLts eating initial (Formula.forallGlobally (.existsNext .top)) :=
  check_iff.mp (by decide +kernel)

/-- **Under a butler every philosopher can always still eat.** In the dining philosophers
transition system of the naive protocol under a butler, for each philosopher
$i \in \{0, 1, 2\}$, from every state reachable from the initial state (all three philosophers
thinking) a state in which philosopher $i$ eats is reachable, in zero or more steps. -/
theorem butler_can_eat (i : Fin 3) :
    Satisfies butlerLts eating initial
      (Formula.forallGlobally (Formula.existsFinally (.atom i))) := by
  revert i
  decide +kernel

/-- **Mutual exclusion under a butler.** In the dining philosophers transition system of the
naive protocol under a butler, for each philosopher $i \in \{0, 1, 2\}$, in no state reachable
from the initial state (all three philosophers thinking) do philosopher $i$ and its neighbour
$i + 1$ (modulo $3$) both eat. -/
theorem butler_mutex (i : Fin 3) :
    Satisfies butlerLts eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

end Cslib.Algorithms.Concurrency.DiningPhilosophers
