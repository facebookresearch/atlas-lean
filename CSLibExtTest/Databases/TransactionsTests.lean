/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.TwoPhaseLocking
public meta import CSLibExt.Databases.TwoPhaseLocking

/-!
# Tests for conflict serializability and two-phase locking

Two transactions `0, 1` and two items `x, y = 0, 1`.
* The lost update `r₀[x] w₁[x] w₀[x]` has the precedence cycle `0 → 1 → 0` and is not
  conflict-serializable.
* `r₀[x] r₁[y] w₀[x] r₁[x]` has the single edge `0 → 1`; serializing in the order `0, 1` gives the
  conflict-equivalent serial schedule `r₀[x] w₀[x] r₁[y] r₁[x]`.
* Repeated accesses are distinct steps: `w₀[x] w₁[x] w₀[x]` is not serial.
* A legal, well-formed two-phase locked schedule (not strict: transaction `0` releases `x` before
  its last write) and a strict one; their reads and writes are conflict-serializable.
* Releasing a lock early and locking again (not two-phase) can produce the lost update, although
  the schedule is well-formed and legal; a schedule in which both transactions hold exclusive
  locks on `x` is not legal; a schedule that never releases a lock is not well-formed.
-/

@[expose] public section

namespace Cslib.Databases.TransactionsTests

open Cslib.Databases Cslib.Algorithms.Lean
open scoped List

/-- `r_i[x]`, the occurrence `k` of transaction `i`. -/
abbrev r (i : Fin 2) (k : ℕ) (x : Fin 2) : Op 2 (Fin 2) := ⟨i, k, .read, x⟩

/-- `w_i[x]`, the occurrence `k` of transaction `i`. -/
abbrev w (i : Fin 2) (k : ℕ) (x : Fin 2) : Op 2 (Fin 2) := ⟨i, k, .write, x⟩

/-- The lost update `r₀[x] w₁[x] w₀[x]`. -/
def lostUpdate : List (Op 2 (Fin 2)) := [r 0 0 0, w 1 0 0, w 0 1 0]

example : PrecedenceEdge lostUpdate 0 1 ∧ PrecedenceEdge lostUpdate 1 0 := by decide

theorem lostUpdate_not_conflictSerializable : ¬ ConflictSerializable lostUpdate := by
  intro h
  apply ConflictSerializable.isAcyclic (by decide) h
  refine ⟨[0, 1], (TopologicalSort.directedCycleIn_iff _ _ _).2
    ⟨by simp, by decide, ?_, ?_, by simp [precedenceGraph]⟩⟩
  · exact List.isChain_pair.mpr (edge_precedenceGraph.mpr (by decide))
  · exact edge_precedenceGraph.mpr (by decide)

/-- `r₀[x] r₁[y] w₀[x] r₁[x]`. -/
def good : List (Op 2 (Fin 2)) := [r 0 0 0, r 1 0 1, w 0 1 0, r 1 1 0]

example : PrecedenceEdge good 0 1 ∧ ¬ PrecedenceEdge good 1 0 := by decide

theorem good_order : TopologicalSort.IsTopologicalOrder (precedenceGraph good) [0, 1] := by
  refine ⟨by decide, fun v => ?_, ?_⟩
  · simp only [precedenceGraph, List.mem_finRange, iff_true]
    revert v
    decide
  intro u v h
  rw [edge_precedenceGraph] at h
  revert h
  revert u v
  decide

#guard serialize [0, 1] good == [r 0 0 0, w 0 1 0, r 1 0 1, r 1 1 0]

/-- Repeated writes of transaction `0` to `x` are distinct steps: `w₀[x] w₁[x] w₀[x]` interleaves
the transactions, so it is not serial, and its precedence graph has edges both ways. -/
example : ¬ IsSerial [w 0 0 0, w 1 0 0, w 0 1 0] ∧ PrecedenceEdge [w 0 0 0, w 1 0 0, w 0 1 0] 0 1 ∧
    PrecedenceEdge [w 0 0 0, w 1 0 0, w 0 1 0] 1 0 := by
  decide

example : IsSerial (serialize [0, 1] good) ∧ ConflictEquiv good (serialize [0, 1] good) :=
  ⟨isSerial_serialize good (by decide), conflictEquiv_serialize (by decide) good_order⟩

example : ConflictSerializable good :=
  ⟨_, isSerial_serialize good (by decide), conflictEquiv_serialize (by decide) good_order⟩

/-! ### Two-phase locking -/

/-- A two-phase schedule: `0` write-locks `x`, writes it, write-locks `y`, releases `x`; then `1`
read-locks and reads `x` while `0` writes `y`. -/
def twoPhase : List (Action 2 (Fin 2)) :=
  [.lock 0 0 .exclusive, .op (w 0 0 0), .lock 0 1 .exclusive, .unlock 0 0, .lock 1 0 .shared,
    .op (r 1 0 0), .op (w 0 1 1), .unlock 0 1, .unlock 1 0]

example : WellFormed twoPhase ∧ Legal twoPhase ∧ TwoPhase twoPhase := by decide

/-- Not strict: `0` releases its exclusive lock on `x` before its last write. -/
example : ¬ StrictTwoPhase twoPhase := by decide

example : ops twoPhase = [w 0 0 0, r 1 0 0, w 0 1 1] := by decide

example : ConflictSerializable (ops twoPhase) :=
  TwoPhase.conflictSerializable (by decide) (by decide) (by decide) (by decide)

/-- A strict two-phase schedule. -/
def strict : List (Action 2 (Fin 2)) :=
  [.lock 0 0 .exclusive, .op (w 0 0 0), .lock 0 1 .exclusive, .op (w 0 1 1), .unlock 0 0,
    .unlock 0 1, .lock 1 0 .shared, .op (r 1 0 0), .unlock 1 0]

example : WellFormed strict ∧ Legal strict ∧ StrictTwoPhase strict := by decide

example : ConflictSerializable (ops strict) :=
  StrictTwoPhase.conflictSerializable (by decide) (by decide) (by decide) (by decide)

/-- Not two-phase: `0` releases its shared lock on `x` and later locks `x` again. -/
def earlyRelease : List (Action 2 (Fin 2)) :=
  [.lock 0 0 .shared, .op (r 0 0 0), .unlock 0 0, .lock 1 0 .exclusive, .op (w 1 0 0),
    .unlock 1 0, .lock 0 0 .exclusive, .op (w 0 1 0), .unlock 0 0]

example : WellFormed earlyRelease ∧ Legal earlyRelease ∧ ¬ TwoPhase earlyRelease := by decide

/-- ... and its reads and writes are the lost update, so the two-phase hypothesis is needed. -/
example : ¬ ConflictSerializable (ops earlyRelease) := by
  have : ops earlyRelease = lostUpdate := by decide
  rw [this]
  exact lostUpdate_not_conflictSerializable

/-- Both transactions hold exclusive locks on `x` at once: not legal. -/
example : ¬ Legal ([.lock 0 0 .exclusive, .lock 1 0 .exclusive] : List (Action 2 (Fin 2))) := by
  decide

/-- An exclusive and a shared lock on `x` by different transactions at once: not legal. -/
example : ¬ Legal ([.lock 0 0 .exclusive, .lock 1 0 .shared] : List (Action 2 (Fin 2))) := by
  decide

/-- A write covered only by a shared lock is not covered. -/
example : ¬ LocksCover ([.lock 0 0 .shared, .op (w 0 0 0)] : List (Action 2 (Fin 2))) := by
  decide

/-- Shared locks coexist; legality is decidable for any item type with decidable equality. -/
example : Legal ([.lock 0 "x" .shared, .lock 1 "x" .shared] : List (Action 2 String)) := by
  decide

/-- A transaction that keeps its lock: the access is covered, but the schedule is not
well-formed. -/
example : LocksCover ([.lock 0 0 .shared, .op (r 0 0 0)] : List (Action 2 (Fin 2))) ∧
    ¬ WellFormed ([.lock 0 0 .shared, .op (r 0 0 0)] : List (Action 2 (Fin 2))) := by
  decide

end Cslib.Databases.TransactionsTests
