/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.DiningPhilosophers

/-!
# Tests for the dining philosophers

* Under the naive protocol, three moves (each philosopher picks up its left
  fork) reach the deadlock.
* Under the ordered protocol philosopher `2` starts with fork `0`, so it
  cannot pick up a fork while philosopher `0` holds fork `0`, and no deadlock
  is reachable.
* Without fairness a philosopher may starve even under the ordered protocol:
  `AF eating 0` fails, while `EF eating 0` holds.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.DiningPhilosophers.Tests

open Cslib.CTL

/-- The deadlocking schedule of the naive protocol. -/
example : (lts naive).Tr initial 0 (1, 0, 0) ∧ (lts naive).Tr (1, 0, 0) 1 (1, 1, 0) ∧
    (lts naive).Tr (1, 1, 0) 2 (1, 1, 1) := by decide

/-- In the deadlock nobody can move. -/
example (i : Fin 3) (t : State) : ¬ (lts naive).Tr (1, 1, 1) i t := by
  revert i t; decide

example : ordered.first 2 = 0 ∧ ordered.second 2 = 2 := by decide

/-- Under the ordered protocol no deadlock is reachable, stated as the failure
of `EF deadlock`. -/
example : ¬ Satisfies (lts ordered) eating initial (Formula.existsFinally deadlock) := by
  decide +kernel

/-- The state where everybody holds its first fork is not reachable under the
ordered protocol: philosophers `0` and `2` both start with fork `0`. -/
example : ¬ (lts ordered).Tr (1, 1, 0) 2 (1, 1, 1) := by decide

/-- Starvation without fairness: philosopher `0` need not eat on every path. -/
example : ¬ Satisfies (lts ordered) eating initial (Formula.forallFinally (.atom 0)) := by
  decide +kernel

/-- ... although it can always still eat. -/
example : Satisfies (lts ordered) eating initial (Formula.existsFinally (.atom 0)) := by
  decide +kernel

end Cslib.Algorithms.Concurrency.DiningPhilosophers.Tests
