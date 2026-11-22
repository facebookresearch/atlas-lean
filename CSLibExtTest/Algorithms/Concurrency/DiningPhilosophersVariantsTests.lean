/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.DiningPhilosophersVariants

/-!
# Tests for atomic acquisition and the butler

* Under atomic acquisition a philosopher goes from thinking straight to eating,
  and not while a neighbour eats.
* The butler stops the third philosopher from picking up a fork, which is the
  move that completes the naive protocol's deadlock.
* Without fairness a philosopher may still starve under both fixes.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.DiningPhilosophers.VariantsTests

open Cslib.CTL

example : atomicLts.Tr initial 0 (2, 0, 0) := by decide

/-- Philosopher `1` cannot start while philosopher `0`, who holds fork `1`,
eats. -/
example (t : State) : ¬ atomicLts.Tr (2, 0, 0) 1 t := by
  revert t; decide

/-- The naive protocol lets philosopher `2` take its left fork while the other
two hold theirs; the butler does not. -/
example : (lts naive).Tr (1, 1, 0) 2 (1, 1, 1) ∧ ¬ butlerLts.Tr (1, 1, 0) 2 (1, 1, 1) := by
  decide

/-- Starvation without fairness under atomic acquisition. -/
example : ¬ Satisfies atomicLts eating initial (Formula.forallFinally (.atom 0)) := by
  decide +kernel

/-- Starvation without fairness under the butler. -/
example : ¬ Satisfies butlerLts eating initial (Formula.forallFinally (.atom 0)) := by
  decide +kernel

end Cslib.Algorithms.Concurrency.DiningPhilosophers.VariantsTests
