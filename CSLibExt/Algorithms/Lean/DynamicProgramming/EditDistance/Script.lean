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

/-- **Edit step.** An edit step over a type $\alpha$ is one of four operations, for
$a, b \in \alpha$: keep $a$ (consume the input value $a$ and reproduce it), delete $a$ (consume
$a$), insert $a$ (produce $a$ without consuming input), or substitute $a$ by $b$ (consume $a$
and produce $b$). -/
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

/-- **Edit script.** An edit script over a type $\alpha$ is a finite list of edit steps over
$\alpha$, applied from left to right. -/
abbrev EditScript (α : Type u) := List (EditStep α)

/-- **Unit cost of an edit step.** The cost of an edit step is $0$ for a keep step and $1$ for a
deletion, an insertion or a substitution. -/
def EditStep.cost : EditStep α → Nat
  | .keep _ => 0
  | .delete _ => 1
  | .insert _ => 1
  | .substitute _ _ => 1

/-- **Cost of an edit script.** The cost of an edit script is the sum of the unit costs of its
steps; the empty script has cost $0$. -/
def EditScript.cost : EditScript α → Nat
  | [] => 0
  | step :: script => step.cost + EditScript.cost script

/-- **Running an edit script.** Over a type $\alpha$ with a boolean equality test, running an
edit script on an input list processes the steps from left to right and either fails or
returns an output list. A keep step with value $a$ consumes the next input value $b$ and
outputs $a$; a deletion of $a$ consumes $b$ and outputs nothing; a substitution of $a$ by $c$
consumes $b$ and outputs $c$. Each of these three fails if the input is exhausted or if the
equality test of $a$ against $b$ fails. An insertion of $c$ outputs $c$ without consuming input.
When the script ends, the run succeeds with the outputs in order if the input is used up, and
fails if input values remain. -/
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

/-- **An edit script transforming one list into another.** Over a type with a boolean equality
test, an edit script transforms a list $x$ into a list $y$ when running the script on $x$
succeeds and outputs $y$. -/
def EditScript.Transforms [BEq α]
    (script : EditScript α) (source target : List α) : Prop :=
  script.apply? source = some target

/-- **Edit-distance result record.** An edit-distance result over a type $\alpha$ consists of a
natural number, the reported distance, and an edit script over $\alpha$.

The record imposes no relation between the two fields; it is meant to hold a minimum edit
distance and a script realizing it. -/
structure EditDistanceResult (α : Type u) where
  /-- Minimum number of non-keep edit operations. -/
  distance : Nat
  /-- A script that realizes the reported distance. -/
  script : EditScript α
  deriving Repr, BEq, DecidableEq

/-- **Edit-distance cost counters.** An edit-distance cost record is a pair of natural numbers:
the number of dynamic-programming table cells initialized or transitioned, and the number of
operations emitted while reconstructing an edit script. -/
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

/-- **Total edit-distance cost.** The total of an edit-distance cost record is the number of table
cells initialized or transitioned plus the number of operations emitted during reconstruction. -/
def EditDistanceCost.total (cost : EditDistanceCost) : Nat :=
  cost.cellTransitions + cost.reconstructionSteps

end Cslib.Algorithms.Lean
