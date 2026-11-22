/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dining philosophers
-/
module

public import CSLibExt.Logics.CTL.ModelChecking
public import Mathlib.Data.Fintype.Prod

/-!
# Dining philosophers, model checked in CTL

Dijkstra's dining philosophers (E. W. Dijkstra, *Hierarchical ordering of
sequential processes*, Acta Informatica 1(2), 1971) with three philosophers and
three forks, checked with the CTL model checker of
`CSLibExt/Logics/CTL/ModelChecking.lean`.

Philosopher `i` sits between fork `i` and fork `i + 1` (modulo 3). A protocol
says which of the two forks each philosopher picks up first. A philosopher
thinks, picks up its first fork when it is free, then its second fork when it
is free, eats, and puts both forks down. One step of the transition system is
one move of one philosopher; a philosopher whose next fork is taken cannot
move, so a state where nobody can move is a deadlock.

* `naive`: everybody picks up the left fork (fork `i`) first. Deadlock is
  reachable (`naive_deadlock_reachable`): all three hold their left fork and
  wait for the right one, a circular wait.
* `ordered`: everybody picks up the lower-numbered fork first, Havender's
  resource ordering (philosopher `2` starts with fork `0`). No deadlock is
  reachable (`ordered_deadlock_free`), and from every reachable state each
  philosopher can still get to eat (`ordered_can_eat`).
* In both protocols neighbours never eat at the same time (`naive_mutex`,
  `ordered_mutex`).

The properties are CTL formulas checked by `check` and `decide +kernel`; there
are 27 states.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.DiningPhilosophers

open Cslib.CTL

/-- The phases of the three philosophers: `0` thinking, `1` holding the first
fork, `2` eating (holding both forks). -/
abbrev State := Fin 3 × Fin 3 × Fin 3

/-- The phase of philosopher `i`. -/
def phase (s : State) : Fin 3 → Fin 3
  | 0 => s.1
  | 1 => s.2.1
  | 2 => s.2.2

/-- Set the phase of philosopher `i`. -/
def setPhase (s : State) (i : Fin 3) (p : Fin 3) : State :=
  match i with
  | 0 => (p, s.2.1, s.2.2)
  | 1 => (s.1, p, s.2.2)
  | 2 => (s.1, s.2.1, p)

/-- A protocol: the fork each philosopher picks up first and the one it picks
up second.  The two forks of philosopher `i` are its two neighbouring forks,
`i` and `i + 1`, in some order (the `neighbours` invariant). -/
structure Protocol where
  /-- The fork picked up first. -/
  first : Fin 3 → Fin 3
  /-- The fork picked up second. -/
  second : Fin 3 → Fin 3
  /-- The two forks are the two neighbouring forks, in some order. -/
  neighbours : ∀ i, (first i = i ∧ second i = i + 1) ∨
    (first i = i + 1 ∧ second i = i)

/-- Whether fork `f` is held by some philosopher. -/
def held (P : Protocol) (s : State) (f : Fin 3) : Bool :=
  [0, 1, 2].any fun (i : Fin 3) =>
    (P.first i == f && decide (1 ≤ (phase s i).val)) || (P.second i == f && phase s i == 2)

/-- Whether philosopher `i` can move: pick up its first fork, pick up its
second fork, or (after eating) put both down. -/
def canMove (P : Protocol) (s : State) (i : Fin 3) : Bool :=
  match (phase s i).val with
  | 0 => !held P s (P.first i)
  | 1 => !held P s (P.second i)
  | _ => true

/-- The move of philosopher `i`: thinking to holding one fork, to eating, to
thinking. -/
def move (s : State) (i : Fin 3) : State :=
  setPhase s i (match (phase s i).val with | 0 => 1 | 1 => 2 | _ => 0)

/-- The transition system of a protocol; the label is the philosopher that
moves. -/
def lts (P : Protocol) : LTS State (Fin 3) where
  Tr s i t := canMove P s i = true ∧ t = move s i

instance (P : Protocol) (s : State) (i : Fin 3) (t : State) :
    Decidable ((lts P).Tr s i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The atom `i` holds when philosopher `i` eats. -/
def eating : State → Fin 3 → Prop := fun s i => phase s i = 2

instance (s : State) (i : Fin 3) : Decidable (eating s i) :=
  inferInstanceAs (Decidable (_ = _))

/-- Everybody thinking. -/
def initial : State := (0, 0, 0)

/-- Everybody picks up the left fork first. -/
def naive : Protocol := ⟨fun i => i, fun i => i + 1, fun _ => Or.inl ⟨rfl, rfl⟩⟩

/-- Everybody picks up the lower-numbered fork first. -/
def ordered : Protocol :=
  ⟨fun i => min i (i + 1), fun i => max i (i + 1), by decide⟩

/-- A deadlock: no philosopher can move. -/
def deadlock : Formula (Fin 3) := .not (.existsNext .top)

/-- Neighbours `i` and `i + 1` do not eat together. -/
def neighboursApart (i : Fin 3) : Formula (Fin 3) :=
  .not (.and (.atom i) (.atom (i + 1)))

/-- **The naive protocol can deadlock.** -/
theorem naive_deadlock_reachable :
    Satisfies (lts naive) eating initial (Formula.existsFinally deadlock) :=
  check_iff.mp (by decide +kernel)

/-- The deadlock: everybody holds the left fork. -/
theorem naive_deadlock_state : Satisfies (lts naive) eating (1, 1, 1) deadlock :=
  check_iff.mp (by decide +kernel)

/-- **Resource ordering prevents deadlock**: under the ordered protocol every
reachable state has a move. -/
theorem ordered_deadlock_free :
    Satisfies (lts ordered) eating initial (Formula.forallGlobally (.existsNext .top)) :=
  check_iff.mp (by decide +kernel)

/-- Under the ordered protocol, from every reachable state each philosopher can
still get to eat. -/
theorem ordered_can_eat (i : Fin 3) :
    Satisfies (lts ordered) eating initial
      (Formula.forallGlobally (Formula.existsFinally (.atom i))) := by
  revert i
  decide +kernel

/-- Neighbours never eat together under the naive protocol. -/
theorem naive_mutex (i : Fin 3) :
    Satisfies (lts naive) eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

/-- Neighbours never eat together under the ordered protocol. -/
theorem ordered_mutex (i : Fin 3) :
    Satisfies (lts ordered) eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

end Cslib.Algorithms.Concurrency.DiningPhilosophers
