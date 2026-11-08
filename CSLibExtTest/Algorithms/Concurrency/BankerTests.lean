/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Concurrency.Banker
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the banker's algorithm

The standard textbook example (Silberschatz, Galvin and Gagne, *Operating
System Concepts*, 9th edition, Section 7.5.3, the banker's-algorithm
illustrative example): five processes `P0`-`P4`, three resource types with free
vector `(3, 3, 2)`.

* The state is safe, witnessed by the safe sequence `P1, P3, P4, P2, P0`, and
  the safety check agrees. Starting `P0` first is not safe.
* `P1`'s request `(1, 0, 2)` is granted.
* After that, `P4`'s request `(3, 3, 0)` exceeds the free resources and `P0`'s
  request `(0, 2, 0)` would lead to an unsafe state; both are refused.
* With too few free resources the state is unsafe and the check fails.
* Requests beyond the remaining claim, beyond the free resources, by a process
  that is not pending, or against a pending list with repetitions are refused.
* The safety check rejects a pending list that repeats a process, which would
  otherwise credit that process's allocation twice.
-/

@[expose] public section

namespace Cslib.Algorithms.Concurrency.Banker.Tests

open _root_.Cslib.Algorithms.Concurrency.Banker.System

/-- Maximum claims and allocations of `P0`–`P4` over resource types `A, B, C`. -/
def S : System (Fin 5) (Fin 3) where
  claim := ![![7, 5, 3], ![3, 2, 2], ![9, 0, 2], ![2, 2, 2], ![4, 3, 3]]
  alloc := ![![0, 1, 0], ![2, 0, 0], ![3, 0, 2], ![2, 1, 1], ![0, 0, 2]]

def available : Fin 3 → ℕ := ![3, 3, 2]

def all : List (Fin 5) := [0, 1, 2, 3, 4]

example : S.need 0 = ![7, 4, 3] := by decide

/-- The textbook safe sequence. -/
example : S.SafeSeq available [1, 3, 4, 2, 0] := by
  simp only [safeSeq_cons, safeSeq_nil, and_true]
  decide

/-- `P0` cannot go first: its need `(7, 4, 3)` exceeds `(3, 3, 2)`. -/
example : ¬ S.SafeSeq available [0, 1, 2, 3, 4] := by
  simp only [safeSeq_cons, safeSeq_nil, and_true]
  decide

example : S.safetyCheck available all = true := by decide

example : S.Safe available all := (safetyCheck_iff _ _).mp (by decide)

/-- With only `(1, 1, 1)` free the state is unsafe: `P3` and then `P1` can
finish, but `P0`, `P2` and `P4` are then stuck at `(5, 2, 2)`. -/
example : ¬ S.Safe ![1, 1, 1] all := fun h => by
  rw [← safetyCheck_iff] at h
  exact absurd h (by decide)

/-- `P1` requests `(1, 0, 2)`: granted. -/
example : (request S available all 1 ![1, 0, 2]).isSome = true := by decide

/-- The state after granting `P1`'s request. -/
def S₁ : System (Fin 5) (Fin 3) := S.grant 1 ![1, 0, 2]

def available₁ : Fin 3 → ℕ := available - ![1, 0, 2]

example : available₁ = ![2, 3, 0] := by decide

example : S₁.Safe available₁ all := (safetyCheck_iff _ _).mp (by decide)

/-- `P4` requests `(3, 3, 0)`: more than is free, refused. -/
example : request S₁ available₁ all 4 ![3, 3, 0] = none := by decide

/-- `P0` requests `(0, 2, 0)`: within its need and the free resources, but the
resulting state is unsafe, so it is refused. -/
example : request S₁ available₁ all 0 ![0, 2, 0] = none := by decide

example : ¬ (S₁.grant 0 ![0, 2, 0]).Safe (available₁ - ![0, 2, 0]) all := fun h => by
  rw [← safetyCheck_iff] at h
  exact absurd h (by decide)

/-- `P1` asks for `(2, 0, 0)`, more than its remaining claim `(1, 2, 2)`. -/
example : request S available all 1 ![2, 0, 0] = none := by decide

/-- `P0` asks for `(4, 0, 0)`: within its claim, but more than is free. -/
example : request S available all 0 ![4, 0, 0] = none := by decide

/-- A request by a process that is not pending is refused. -/
example : request S available [1, 2, 3, 4] 0 ![0, 0, 0] = none := by decide

/-- A pending list with a repetition is refused. -/
example : request S available [0, 1, 1, 2, 3, 4] 1 ![1, 0, 2] = none := by decide

/-- One resource; `P0` holds its whole claim of `1`, `P1` claims `2` and holds
nothing, and nothing is free. -/
def T : System (Fin 2) (Fin 1) where
  claim := ![![1], ![2]]
  alloc := ![![1], ![0]]

/-- The state is unsafe: after `P0` finishes only `1` is free. -/
example : T.safetyCheck 0 [0, 1] = false := by decide

/-- Listing `P0` twice would credit its allocation twice; the check rejects
the list. -/
example : T.safetyCheck 0 [0, 0, 1] = false := by decide

example : ¬ T.Safe 0 [0, 0, 1] := fun h => by
  rw [← safetyCheck_iff] at h
  exact absurd h (by decide)

/-- The granted request of `P1` produces the expected state. -/
example : request S available all 1 ![1, 0, 2] = some (available₁, S₁) :=
  request_eq_some_iff.mpr ⟨by decide, by decide, by decide, by decide,
    (safetyCheck_iff _ _).mp (by decide), rfl, rfl⟩

end Cslib.Algorithms.Concurrency.Banker.Tests
