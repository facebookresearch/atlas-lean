/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

/-!
# Edit scripts

Unit-cost insertion, deletion, substitution, and zero-cost retention operations for generic
lists. An executable script records the values it consumes, so malformed scripts are rejected.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- One alignment step in a unit-cost edit script. -/
inductive EditStep (α : Type u) where
  /-- Consume and reproduce the given value at zero cost. -/
  | keep (value : α)
  /-- Consume the given value. -/
  | delete (value : α)
  /-- Produce the given value without consuming input. -/
  | insert (value : α)
  /-- Consume the first value and produce the second. -/
  | substitute (source target : α)
  deriving Repr, BEq, DecidableEq

/-- A left-to-right sequence of edit operations. -/
abbrev EditScript (α : Type u) := List (EditStep α)

/-- Unit cost of an edit step. Keeps are free and the three edits cost one. -/
def EditStep.cost : EditStep α → Nat
  | .keep _ => 0
  | .delete _ => 1
  | .insert _ => 1
  | .substitute _ _ => 1

/-- Sum of the unit costs of a script. -/
def EditScript.cost : EditScript α → Nat
  | [] => 0
  | step :: script => step.cost + EditScript.cost script

/-- Execute a script, rejecting a stored source value that does not match the next input value. -/
def EditScript.apply? [BEq α] : EditScript α → List α → Option (List α)
  | [], [] => some []
  | [], _ :: _ => none
  | .keep value :: script, source :: rest =>
      if value == source then (EditScript.apply? script rest).map (value :: ·) else none
  | .keep _ :: _, [] => none
  | .delete value :: script, source :: rest =>
      if value == source then EditScript.apply? script rest else none
  | .delete _ :: _, [] => none
  | .insert value :: script, source =>
      (EditScript.apply? script source).map (value :: ·)
  | .substitute value target :: script, source :: rest =>
      if value == source then (EditScript.apply? script rest).map (target :: ·) else none
  | .substitute _ _ :: _, [] => none

/-- A script transforms a source when its executable interpretation returns the target. -/
def EditScript.Transforms [BEq α]
    (script : EditScript α) (source target : List α) : Prop :=
  script.apply? source = some target

/-- A minimum edit distance together with one deterministic realizing script. -/
structure EditDistanceResult (α : Type u) where
  /-- Minimum number of non-keep edit operations. -/
  distance : Nat
  /-- A script that realizes the reported distance. -/
  script : EditScript α
  deriving Repr, BEq, DecidableEq

/-- Counts table cells and emitted reconstruction steps separately. -/
structure EditDistanceCost where
  /-- Dynamic-programming cells initialized or transitioned. -/
  cellTransitions : Nat
  /-- Operations emitted while reconstructing a script. -/
  reconstructionSteps : Nat
  deriving Repr, BEq, DecidableEq

instance : Zero EditDistanceCost where
  zero := ⟨0, 0⟩

instance : Add EditDistanceCost where
  add left right :=
    ⟨left.cellTransitions + right.cellTransitions,
      left.reconstructionSteps + right.reconstructionSteps⟩

instance : AddMonoid EditDistanceCost where
  add_assoc left middle right := by
    rcases left with ⟨leftCells, leftReconstruction⟩
    rcases middle with ⟨middleCells, middleReconstruction⟩
    rcases right with ⟨rightCells, rightReconstruction⟩
    change EditDistanceCost.mk (leftCells + middleCells + rightCells)
      (leftReconstruction + middleReconstruction + rightReconstruction) =
      EditDistanceCost.mk (leftCells + (middleCells + rightCells))
        (leftReconstruction + (middleReconstruction + rightReconstruction))
    rw [Nat.add_assoc, Nat.add_assoc]
  zero_add cost := by
    rcases cost with ⟨cells, reconstruction⟩
    change EditDistanceCost.mk (0 + cells) (0 + reconstruction) =
      EditDistanceCost.mk cells reconstruction
    simp
  add_zero cost := by
    rcases cost with ⟨cells, reconstruction⟩
    change EditDistanceCost.mk (cells + 0) (reconstruction + 0) =
      EditDistanceCost.mk cells reconstruction
    simp
  nsmul count cost :=
    ⟨count * cost.cellTransitions, count * cost.reconstructionSteps⟩
  nsmul_zero cost := by
    rcases cost with ⟨cells, reconstruction⟩
    change EditDistanceCost.mk (0 * cells) (0 * reconstruction) =
      EditDistanceCost.mk 0 0
    simp
  nsmul_succ count cost := by
    rcases cost with ⟨cells, reconstruction⟩
    change EditDistanceCost.mk ((count + 1) * cells) ((count + 1) * reconstruction) =
      EditDistanceCost.mk (count * cells + cells) (count * reconstruction + reconstruction)
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]

/-- Total charged events in the edit-distance cost model. -/
def EditDistanceCost.total (cost : EditDistanceCost) : Nat :=
  cost.cellTransitions + cost.reconstructionSteps

end Cslib.Algorithms.Lean
