/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.BakeryNProcesses

/-!
# Tests for Lamport's bakery algorithm for `N` processes

* Lamport's order on (ticket, name) pairs: equal tickets are ordered by name.
* Non-vacuity: with two processes, process `0` reaches its critical section in eleven steps
  (L1, two reads, the end of the reads, the write of its ticket `1`, the reset of `choosing`,
  and L2/L3 for `j = 0, 1`), so the mutual exclusion theorem is about reachable critical
  sections.
* In that state process `1`, in its noncritical section, is not in its critical section.
* Contention: process `0` enters its critical section while process `1` holds a larger ticket
  and waits at L2; Assertion 2 orders their (ticket, name) pairs.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.BakeryNProcesses.Tests

example : Before 3 (0 : Fin 2) 3 1 := Or.inr ⟨rfl, by decide⟩
example : ¬ Before 3 (1 : Fin 2) 3 0 := by unfold Before; decide

/-- Process `0` of two reaches its critical section. -/
theorem exists_cs : ∃ s : State 2, lts.CanReach init s ∧ s.pc 0 = .cs := by
  refine ⟨?s, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ?run⟩, ?hcs⟩
  case run =>
    refine .stepL ⟨_, _, _, LocalStep.enter (by simp [init]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.read _ _ 0 rfl (by decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.read _ _ 1 rfl (by decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.endRead 0 (by simp [setLocal, init]; decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.write _ rfl, rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.exit (by simp [setLocal]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l2 0 (by decide) (by simp [setLocal])
      (by simp [setLocal]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l3 0 (by decide) (by simp [setLocal])
      (by simp [setLocal, Before]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l2 1 (by decide) (by simp [setLocal])
      (by simp [setLocal, init]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l3 1 (by decide) (by simp [setLocal])
      (by simp [setLocal, init]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.enterCS (by simp [setLocal]), rfl⟩ ?_
    exact .refl
  case hcs => simp [setLocal]

/-- In that state the other process is not in its critical section, as mutual exclusion
requires. -/
example : ∃ s : State 2, lts.CanReach init s ∧ s.pc 0 = .cs ∧ s.pc 1 ≠ .cs := by
  obtain ⟨s, hs, h0⟩ := exists_cs
  exact ⟨s, hs, h0, fun h1 => absurd (mutual_exclusion hs h0 h1) (by decide)⟩

/-- Contention: process `0` takes ticket `1`, then process `1` reads it and takes ticket `2`;
process `0` passes both loop indices and enters its critical section while process `1` holds
the larger ticket and waits at L2. -/
theorem exists_cs_contended : ∃ s : State 2, lts.CanReach init s ∧ s.pc 0 = .cs ∧
    s.pc 1 = .l2 0 ∧ s.number 0 = 1 ∧ s.number 1 = 2 := by
  refine ⟨?s, ⟨[0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], ?run⟩, ?hcs⟩
  case run =>
    refine .stepL ⟨_, _, _, LocalStep.enter (by simp [init]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.read _ _ 0 rfl (by decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.read _ _ 1 rfl (by decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.endRead 0 (by simp [setLocal, init]; decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.write _ rfl, rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.exit (by simp [setLocal]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.enter (by simp [setLocal, init]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.read _ _ 0 rfl (by decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.read _ _ 1 rfl (by decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.endRead 1 (by simp [setLocal, init]; decide), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.write _ rfl, rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.exit (by simp [setLocal]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l2 0 (by decide) (by simp [setLocal])
      (by simp [setLocal]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l3 0 (by decide) (by simp [setLocal])
      (by simp [setLocal, Before]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l2 1 (by decide) (by simp [setLocal])
      (by simp [setLocal]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.l3 1 (by decide) (by simp [setLocal])
      (by simp [setLocal, init, Before]), rfl⟩ ?_
    refine .stepL ⟨_, _, _, LocalStep.enterCS (by simp [setLocal]), rfl⟩ ?_
    exact .refl
  case hcs => simp [setLocal, init]

/-- In the contended state, Assertion 2 orders the ticket holders: `(1, 0) < (2, 1)`. -/
example : ∃ s : State 2, lts.CanReach init s ∧ s.pc 0 = .cs ∧ s.pc 1 ≠ .cs ∧
    Before (s.number 0) (0 : Fin 2) (s.number 1) 1 := by
  obtain ⟨s, hs, h0, h1, -, -⟩ := exists_cs_contended
  exact ⟨s, hs, h0, by simp [h1], before_of_cs hs h0 (by simp [h1, HasTicket]) (by decide)⟩

end Cslib.Algorithms.Concurrency.BakeryNProcesses.Tests
