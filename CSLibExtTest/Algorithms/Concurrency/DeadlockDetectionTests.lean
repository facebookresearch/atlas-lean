/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.DeadlockDetection
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for deadlock detection

The example of Silberschatz, Galvin and Gagne, *Operating System Concepts*,
9th edition, Section 7.6.2: five processes and three resource types with
`7`, `2` and `6` instances, nothing free.

* With the original requests nothing is reported: the textbook's sequence
  `P0, P2, P3, P1, P4` finishes everybody.
* When `P2` also requests one instance of `C`, `P1`, `P2`, `P3` and `P4` are
  reported, as in the textbook; only `P0` can finish, and it releases too
  little.
* The report does not depend on the order of the pending list.
* A process that holds nothing but waits for a deadlocked resource holder is
  reported too (Holt's permanently blocked processes).
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.DeadlockDetection.Tests

open State

/-- Allocations of the textbook example. -/
def alloc : Fin 5 → Fin 3 → ℕ :=
  ![![0, 1, 0], ![2, 0, 0], ![3, 0, 3], ![2, 1, 1], ![0, 0, 2]]

/-- The textbook state without deadlock. -/
def ok : State (Fin 5) (Fin 3) :=
  ⟨alloc, ![![0, 0, 0], ![2, 0, 2], ![0, 0, 0], ![1, 0, 0], ![0, 0, 2]]⟩

/-- The textbook state after `P2` requests one more instance of `C`. -/
def stuck : State (Fin 5) (Fin 3) :=
  ⟨alloc, ![![0, 0, 0], ![2, 0, 2], ![0, 0, 1], ![1, 0, 0], ![0, 0, 2]]⟩

/-- Nothing is free. -/
def none0 : Fin 3 → ℕ := 0

example : ok.detect none0 [0, 1, 2, 3, 4] = [] := by decide

/-- The textbook's sequence finishes everybody. -/
example : ok.Reduces none0 [0, 2, 3, 1, 4] := by decide

example : stuck.detect none0 [0, 1, 2, 3, 4] = [1, 2, 3, 4] := by decide

example : stuck.finished none0 [0, 1, 2, 3, 4] = [0] := by decide

/-- The same processes are reported for another order of the pending list. -/
example : stuck.detect none0 [4, 3, 2, 1, 0] = [4, 3, 2, 1] := by decide

/-- `P1` is deadlocked: no reduction sequence finishes it. -/
example : ¬ ∃ σ, stuck.Reduces none0 σ ∧ σ.Nodup ∧ σ ⊆ [0, 1, 2, 3, 4] ∧ (1 : Fin 5) ∈ σ :=
  ((mem_detect_iff (by decide)).1 (by decide)).2

/-- `P2` is stuck even after `P0` releases its allocation. -/
example : ¬ stuck.request 2 ≤ none0 + ((stuck.finished none0 [0, 1, 2, 3, 4]).map alloc).sum :=
  detect_stuck none0 [0, 1, 2, 3, 4] 2 (by decide)

/-- No ordering of the five processes finishes them all. -/
example : ¬ ∃ σ, σ.Perm [0, 1, 2, 3, 4] ∧ stuck.Reduces none0 σ := fun h =>
  absurd ((detect_eq_nil_iff (S := stuck) (work := none0) (by decide)).2 h) (by decide)

/-- Two single-instance resources: `P0` holds `r0` and waits for `r1`, `P1`
holds `r1` and waits for `r0`, and `P2` holds nothing and waits for `r0`. -/
def cycle : State (Fin 3) (Fin 2) :=
  ⟨![![1, 0], ![0, 1], ![0, 0]], ![![0, 1], ![1, 0], ![1, 0]]⟩

/-- All three are permanently blocked, including `P2`, which holds nothing; the
textbook version would mark `P2` finished at the start and report only `P0`
and `P1`. -/
example : cycle.detect 0 [0, 1, 2] = [0, 1, 2] := by decide

example : (cycle.detect 0 [0, 1, 2]).filter (fun p => cycle.alloc p ≠ 0) = [0, 1] := by decide

end Cslib.Algorithms.Concurrency.DeadlockDetection.Tests
