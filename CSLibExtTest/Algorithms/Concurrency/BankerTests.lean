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

/-! ## The bridge to deadlock detection -/

/-- The banker's safety check and deadlock detection with the remaining needs
as requests agree: the unsafe state leaves `P1` reported as deadlocked. -/
example : T.toDetectionState.detect 0 [0, 1] = [1] := by decide

example : ¬ T.Safe 0 [0, 1] := fun h => by
  have := ((T.safe_iff_detect_eq_nil 0 [0, 1]).mp h).2
  exact absurd this (by decide)

/-- Detection alone does not check for repetitions: with `P0` listed twice it
lets both copies finish, credits `P0`'s allocation twice and then finishes
`P1`, while the safety check rejects the list. -/
example : T.toDetectionState.detect 0 [0, 0, 1] = [] ∧ T.safetyCheck 0 [0, 0, 1] = false := by
  decide

example : S.safetyCheck available all = true ↔
    all.Nodup ∧ S.toDetectionState.detect available all = [] :=
  S.safetyCheck_eq_true_iff_detect_eq_nil available all

universe u v

/-- The sequence correspondence works for arbitrary process and resource universes. -/
example {P : Type u} {R : Type v} (B : System P R) (work : R → ℕ) (σ : List P) :
    B.SafeSeq work σ ↔ B.toDetectionState.Reduces work σ :=
  safeSeq_iff_reduces B work σ

/-- The checker correspondence retains duplicate-freeness in arbitrary universes. -/
example {P : Type u} {R : Type v} [DecidableEq P] [Fintype R]
    (B : System P R) (work : R → ℕ) (pending : List P) :
    B.safetyCheck work pending = true ↔
      pending.Nodup ∧ B.toDetectionState.detect work pending = [] :=
  safetyCheck_eq_true_iff_detect_eq_nil B work pending

example : S.toDetectionState.alloc = S.alloc := by simp

example : S.toDetectionState.request = S.need := by simp

/-- Detection with remaining needs finishes the textbook safe state. -/
example : S.toDetectionState.detect available all = [] := by decide

/-- The safety theorem can now use detection directly. -/
example : S.Safe available all :=
  (safe_iff_detect_eq_nil S available all).mpr ⟨by decide, by decide⟩

/-- After `P3` and `P1` finish, only `(5, 2, 2)` is free, so `P0`, `P2`,
and `P4` remain. -/
example : S.toDetectionState.detect ![1, 1, 1] all = [0, 2, 4] := by decide

/-- The correspondence applies to zero fuel without assuming enough rounds. -/
example : S.safetyCheckAux 0 available all = true ↔
    (S.toDetectionState.reduceAux 0 available all).2 = [] :=
  safetyCheckAux_iff_reduceAux S 0 available all

/-- Neither loop succeeds when its fuel stops after only one process finishes. -/
example : S.safetyCheckAux 1 available all = false ∧
    (S.toDetectionState.reduceAux 1 available all).2 ≠ [] := by decide

/-- Repeating a process can make detection release its allocation twice. -/
example : T.toDetectionState.detect 0 [0, 0, 1] = [] := by decide

/-- The sequence bridge still holds for repetitions. It does not assert safety. -/
example : T.SafeSeq 0 [0, 0, 1] :=
  (safeSeq_iff_reduces T 0 [0, 0, 1]).mpr (by decide)

/-- An empty detection report alone cannot make the repeated pending list safe. -/
example : T.toDetectionState.detect 0 [0, 0, 1] = [] ∧
    T.safetyCheck 0 [0, 0, 1] = false ∧ ¬ T.Safe 0 [0, 0, 1] := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact (by decide : ¬ ([0, 0, 1] : List (Fin 2)).Nodup) h.1

/-- Detection's member-erasure lemma does not require that member to fit now. -/
example : S.SafeSeq (available + S.alloc 0) ([1, 3, 4, 2, 0].erase 0) :=
  SafeSeq.erase
    ((safeSeq_iff_reduces S available [1, 3, 4, 2, 0]).mpr (by decide)) (by simp)

/-- Empty process and resource types still give matching successful checks. -/
example :
    let B : System Empty Empty := ⟨(fun p => nomatch p), (fun p => nomatch p)⟩
    B.safetyCheck (fun r => nomatch r) [] = true ∧
      B.toDetectionState.detect (fun r => nomatch r) [] = [] := by decide

/-- With no resource types, a single process needs no resources. -/
example :
    let B : System Unit Empty := ⟨(fun _ r => nomatch r), (fun _ r => nomatch r)⟩
    B.safetyCheck (fun r => nomatch r) [()] = true ∧
      B.toDetectionState.detect (fun r => nomatch r) [()] = [] := by decide

/-- The adapter preserves truncated subtraction even for an allocation above the claim. -/
example :
    let B : System Unit (Fin 1) := ⟨fun _ _ => 0, fun _ _ => 1⟩
    B.toDetectionState.request () = 0 ∧ B.safetyCheck 0 [()] = true := by decide

end Cslib.Algorithms.Concurrency.Banker.Tests
