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

/-- **Dining-philosophers state.** A state of the three dining philosophers is a triple
$(s_0, s_1, s_2)$ with each $s_i \in \{0, 1, 2\}$ the phase of philosopher $i$: $0$ thinking,
$1$ holding the first fork, $2$ eating (holding both forks). -/
abbrev State := Fin 3 × Fin 3 × Fin 3

/-- **Phase of a philosopher.** For a state $s = (s_0, s_1, s_2)$ of the three dining
philosophers and a philosopher $i \in \{0, 1, 2\}$, the phase of philosopher $i$ in $s$ is the
component $s_i$. -/
def phase (s : State) : Fin 3 → Fin 3
  | 0 => s.1
  | 1 => s.2.1
  | 2 => s.2.2

/-- **Updating the phase of a philosopher.** For a state $s = (s_0, s_1, s_2)$ of the three
dining philosophers, a philosopher $i \in \{0, 1, 2\}$ and a phase $p \in \{0, 1, 2\}$, setting
the phase of philosopher $i$ to $p$ gives the state obtained from $s$ by replacing the
component $s_i$ by $p$ and keeping the other two components. -/
def setPhase (s : State) (i : Fin 3) (p : Fin 3) : State :=
  match i with
  | 0 => (p, s.2.1, s.2.2)
  | 1 => (s.1, p, s.2.2)
  | 2 => (s.1, s.2.1, p)

/-- **Dining-philosophers protocol.** A protocol for three philosophers $i \in \{0, 1, 2\}$
sitting between forks $0, 1, 2$ consists of two maps $\mathrm{first}, \mathrm{second}$ from
$\{0, 1, 2\}$ to itself, the fork philosopher $i$ picks up first and the one it picks up
second, such that for every $i$ these are its two neighbouring forks $i$ and $i + 1$
(modulo $3$) in some order: either $\mathrm{first}(i) = i$ and $\mathrm{second}(i) = i + 1$,
or $\mathrm{first}(i) = i + 1$ and $\mathrm{second}(i) = i$. -/
structure Protocol where
  /-- The fork picked up first. -/
  first : Fin 3 → Fin 3
  /-- The fork picked up second. -/
  second : Fin 3 → Fin 3
  /-- The two forks are the two neighbouring forks, in some order. -/
  neighbours : ∀ i, (first i = i ∧ second i = i + 1) ∨
    (first i = i + 1 ∧ second i = i)

/-- **Held forks.** Given a protocol and a state, fork $f$ is held exactly when some philosopher
$i$ either has $f$ as its first fork and is in phase $1$ or $2$, or has $f$ as its second fork
and is in phase $2$ (eating). -/
def held (P : Protocol) (s : State) (f : Fin 3) : Bool :=
  [0, 1, 2].any fun (i : Fin 3) =>
    (P.first i == f && decide (1 ≤ (phase s i).val)) || (P.second i == f && phase s i == 2)

/-- **When a philosopher can move.** Given a protocol and a state, philosopher $i$ can move
exactly when it is thinking (phase $0$) and its first fork is not held by any philosopher, or it
holds its first fork (phase $1$) and its second fork is not held by any philosopher, or it is
eating (phase $2$), in which case its move puts both forks down. -/
def canMove (P : Protocol) (s : State) (i : Fin 3) : Bool :=
  match (phase s i).val with
  | 0 => !held P s (P.first i)
  | 1 => !held P s (P.second i)
  | _ => true

/-- **Move of a philosopher.** The state obtained from $s$ when philosopher $i$ moves: the phase
of $i$ advances from thinking ($0$) to holding its first fork ($1$), from $1$ to eating ($2$),
and from eating back to thinking; the phases of the other philosophers are unchanged. Whether
the move is allowed is not checked here. -/
def move (s : State) (i : Fin 3) : State :=
  setPhase s i (match (phase s i).val with | 0 => 1 | 1 => 2 | _ => 0)

/-- **Transition system of a dining-philosophers protocol.** For a protocol $P$, the labelled
transition system on the states whose labels are the philosophers: there is a transition from
$s$ to $t$ labelled $i$ exactly when philosopher $i$ can move in $s$ under $P$ and $t$ is the
state obtained from $s$ by the move of philosopher $i$. -/
def lts (P : Protocol) : LTS State (Fin 3) where
  Tr s i t := canMove P s i = true ∧ t = move s i

instance (P : Protocol) (s : State) (i : Fin 3) (t : State) :
    Decidable ((lts P).Tr s i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The eating valuation.** The valuation of the atoms $i \in \{0, 1, 2\}$ on the states of the
dining philosophers: atom $i$ holds at a state exactly when philosopher $i$ is eating there, that
is, when its phase is $2$. -/
def eating : State → Fin 3 → Prop := fun s i => phase s i = 2

instance (s : State) (i : Fin 3) : Decidable (eating s i) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Initial state of the dining philosophers.** The state in which all three philosophers are
thinking, that is, every phase is $0$. -/
def initial : State := (0, 0, 0)

/-- **Naive dining-philosophers protocol.** The protocol in which every philosopher
$i \in \{0, 1, 2\}$ picks up fork $i$ (its left fork) first and fork $i + 1$ (modulo $3$) second. -/
def naive : Protocol := ⟨fun i => i, fun i => i + 1, fun _ => Or.inl ⟨rfl, rfl⟩⟩

/-- **Resource-ordered dining-philosophers protocol.** The protocol in which every philosopher
$i \in \{0, 1, 2\}$ picks up the lower-numbered of its two forks $i$ and $i + 1$ (modulo $3$)
first and the higher-numbered one second: philosophers $0$ and $1$ take fork $i$ first, and
philosopher $2$ takes fork $0$ first and fork $2$ second. -/
def ordered : Protocol :=
  ⟨fun i => min i (i + 1), fun i => max i (i + 1), by decide⟩

/-- **The deadlock formula.** The CTL formula $\neg\,\mathsf{EX}\,\top$ over the philosophers as
atoms. It holds at a state exactly when the state has no successor; in the transition system of
a protocol, exactly when no philosopher can move. -/
def deadlock : Formula (Fin 3) := .not (.existsNext .top)

/-- **Neighbours-apart formula.** For a philosopher $i \in \{0, 1, 2\}$, the CTL formula
$\neg(p_i \wedge p_{i+1})$ over the atoms $p_0, p_1, p_2$ (one per philosopher), with indices
modulo $3$. Under the valuation in which $p_j$ holds when philosopher $j$ eats, it says that the
neighbouring philosophers $i$ and $i + 1$ do not eat at the same time. -/
def neighboursApart (i : Fin 3) : Formula (Fin 3) :=
  .not (.and (.atom i) (.atom (i + 1)))

/-- **The naive protocol can deadlock.** Consider the transition system of the naive protocol, in
which every philosopher $i$ picks up fork $i$ first and fork $i + 1$ second (indices modulo $3$),
with atom $i$ read as "philosopher $i$ is eating". Its initial state, where all philosophers are
thinking, satisfies the CTL formula $\mathsf{EF}$ applied to the deadlock formula: from it, a
state in which no philosopher can move is reachable. -/
theorem naive_deadlock_reachable :
    Satisfies (lts naive) eating initial (Formula.existsFinally deadlock) :=
  check_iff.mp (by decide +kernel)

/-- **A deadlock state of the naive protocol.** In the transition system of the naive protocol,
with atom $i$ read as "philosopher $i$ is eating", the state in which every philosopher holds its
first fork (every phase is $1$) satisfies the deadlock formula: no philosopher can move there. -/
theorem naive_deadlock_state : Satisfies (lts naive) eating (1, 1, 1) deadlock :=
  check_iff.mp (by decide +kernel)

/-- **Resource ordering prevents deadlock for the dining philosophers.** In the transition
system of the three dining philosophers under the resource-ordered protocol, the initial state,
in which everybody thinks, satisfies the CTL formula $\mathrm{AG}\,\mathrm{EX}\,\top$: every
state reachable from it has a successor, that is, some philosopher can move. -/
theorem ordered_deadlock_free :
    Satisfies (lts ordered) eating initial (Formula.forallGlobally (.existsNext .top)) :=
  check_iff.mp (by decide +kernel)

/-- **Every philosopher can still eat under resource ordering.** In the transition system of
the three dining philosophers under the resource-ordered protocol, with the atom $p_j$ holding
when philosopher $j$ eats, the initial state, in which everybody thinks, satisfies the CTL
formula $\mathrm{AG}\,\mathrm{EF}\,p_i$ for every philosopher $i \in \{0, 1, 2\}$: from every
state reachable from the initial state, some state in which philosopher $i$ eats is reachable. -/
theorem ordered_can_eat (i : Fin 3) :
    Satisfies (lts ordered) eating initial
      (Formula.forallGlobally (Formula.existsFinally (.atom i))) := by
  revert i
  decide +kernel

/-- **Mutual exclusion under the naive protocol.** For every philosopher $i$, in the transition
system of the naive protocol, with atom $j$ read as "philosopher $j$ is eating", the initial
state satisfies $\mathsf{AG}$ applied to the formula that philosophers $i$ and $i + 1$ (indices
modulo $3$) do not both eat: in no state reachable from the initial state, where all
philosophers are thinking, are philosophers $i$ and $i + 1$ both eating. -/
theorem naive_mutex (i : Fin 3) :
    Satisfies (lts naive) eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

/-- **Neighbours never eat together under resource ordering.** In the transition system of the
three dining philosophers under the resource-ordered protocol, with the atom $p_j$ holding when
philosopher $j$ eats, the initial state, in which everybody thinks, satisfies the CTL formula
$\mathrm{AG}\,\neg(p_i \wedge p_{i+1})$ for every philosopher $i \in \{0, 1, 2\}$, with indices
modulo $3$: in no state reachable from the initial state do philosophers $i$ and $i + 1$ both
eat. -/
theorem ordered_mutex (i : Fin 3) :
    Satisfies (lts ordered) eating initial (Formula.forallGlobally (neighboursApart i)) := by
  revert i
  decide +kernel

end Cslib.Algorithms.Concurrency.DiningPhilosophers
