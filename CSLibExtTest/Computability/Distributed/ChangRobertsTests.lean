/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.ChangRoberts
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for Chang-Roberts leader election

A ring of three processes with identifiers `1, 3, 2`.

* Delivering messages in the order `1, 2, 0, 0, 1, 1` elects process `1`, the
  one with the largest identifier: the safety theorems are not vacuous.
* The theorems then say that process `1` is the only leader.
* After two deliveries, process `1` has discarded the identifier of process
  `0`, and process `2` has forwarded the identifier of process `1` to process
  `0`.
-/

@[expose] public section

namespace Cslib.Distributed.ChangRoberts.Tests

/-- The identifiers. -/
def ids : Fin 3 → ℕ := ![1, 3, 2]

/-- The election run. -/
def schedule : List (Fin 3) := [1, 2, 0, 0, 1, 1]

example : (run ids initial schedule).map (fun s => s.leader 1) = some true := by decide

/-- Process `1` is elected in a reachable state. -/
theorem elected : ∃ s, Reachable ids s ∧ s.leader 1 = true := by
  cases h : run ids initial schedule with
  | none =>
      have : (run ids initial schedule).isSome = true := by decide
      rw [h] at this
      exact absurd this (by decide)
  | some s =>
      refine ⟨s, reachable_of_run schedule (reachable_initial ids) h, ?_⟩
      have : (run ids initial schedule).map (fun s => s.leader 1) = some true := by decide
      rw [h] at this
      simpa using this

/-- In that state nobody else is leader. -/
example : ∃ s, Reachable ids s ∧ s.leader 1 = true ∧ ∀ i, s.leader i = true → i = 1 := by
  obtain ⟨s, hs, h1⟩ := elected
  exact ⟨s, hs, h1, fun i hi => leader_unique hs hi h1⟩

/-- After two deliveries, the identifier of process `0` is gone and the
identifier of process `1` waits at process `0`, behind that of process `2`. -/
example : (run ids initial [1, 2]).map (fun s => (s.chan 0, s.chan 1)) = some ([2, 1], []) := by
  decide

end Cslib.Distributed.ChangRoberts.Tests
