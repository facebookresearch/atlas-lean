/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Foundations.Data.List.IsChainFromTo
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Data.List.Range
public import Mathlib.Data.Vector.Basic

/-!
# Floyd-Warshall foundations

Path semantics, the executable bottom-up matrix recurrence, and its exact event counts. The
algorithm follows CLRS, fourth edition, Section 23.2. It counts one initialization event per
matrix cell and one transition event per `(k, i, j)` triple.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall

/-- Sum the direct weights along a vertex-list path. Empty and singleton lists have weight zero. -/
def pathWeight {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    List (Fin n) → WithTop Int
  | [] => 0
  | [_] => 0
  | source :: target :: rest =>
      weight source target + pathWeight weight (target :: rest)

/-- A nonempty vertex list with the given endpoints and a finite weight on every edge. -/
def IsWeightedPath {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source target : Fin n) (path : List (Fin n)) : Prop :=
  path.IsChainFromTo (fun left right => weight left right ≠ ⊤) source target

/-- Every intermediate vertex in the path has value strictly below `k`. -/
def InternalVerticesBelow {n : Nat} (k : Nat) (path : List (Fin n)) : Prop :=
  ∀ vertex ∈ path.tail.dropLast, vertex.val < k

/-- `distance` is the minimum weight of paths whose intermediate vertices are below `k`. -/
def IsStageShortestPathWeight {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (k : Nat) (source target : Fin n) (distance : WithTop Int) : Prop :=
  (∀ path, IsWeightedPath weight source target path → InternalVerticesBelow k path →
    distance ≤ pathWeight weight path) ∧
  (distance = ⊤ ∨ ∃ path, IsWeightedPath weight source target path ∧
    InternalVerticesBelow k path ∧ pathWeight weight path = distance)

/-- A closed, nonempty, simple vertex-list path of negative weight. -/
def IsNegativeCycle {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (cycle : List (Fin n)) : Prop :=
  ∃ base, IsWeightedPath weight base base cycle ∧ 2 ≤ cycle.length ∧
    cycle.dropLast.Nodup ∧ pathWeight weight cycle < 0

/-- The direct-weight matrix contains a negative cycle. -/
def HasNegativeCycle {n : Nat} (weight : Fin n → Fin n → WithTop Int) : Prop :=
  ∃ cycle, IsNegativeCycle weight cycle

/-- The direct-weight matrix contains no negative cycle. -/
def NoNegativeCycle {n : Nat} (weight : Fin n → Fin n → WithTop Int) : Prop :=
  ¬HasNegativeCycle weight

/-- Separate initialization and min-plus transition event counts. -/
structure Cost where
  /-- Input matrix cells copied and diagonal-normalized. -/
  initializations : Nat
  /-- Executed min-plus table transitions. -/
  transitions : Nat
deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩

instance : Add Cost := ⟨fun left right =>
  ⟨left.initializations + right.initializations, left.transitions + right.transitions⟩⟩

/-- The sum of both abstract event counts. -/
def Cost.total (cost : Cost) : Nat := cost.initializations + cost.transitions

/-- Compute the all-pairs distance matrix by the bottom-up Floyd-Warshall recurrence. -/
@[no_expose]
def floydWarshall {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    TimeM Cost (Fin n → Fin n → WithTop Int) :=
  let Table := Vector (Vector (WithTop Int) n) n
  let tableGet (table : Table) (i j : Fin n) : WithTop Int := (table.get i).get j
  let rec initializeRow (rowIndex : Fin n) :
      (j : Nat) → j ≤ n → TimeM Cost (Vector (WithTop Int) j)
    | 0, _ => pure #v[]
    | j + 1, hj => do
        let row ← initializeRow rowIndex j (by omega)
        TimeM.tick ⟨1, 0⟩
        let column : Fin n := ⟨j, by omega⟩
        let value := min (weight rowIndex column) (if rowIndex = column then 0 else ⊤)
        pure (row.push value)
  let rec buildInitial :
      (i : Nat) → i ≤ n → TimeM Cost (Vector (Vector (WithTop Int) n) i)
    | 0, _ => pure #v[]
    | i + 1, hi => do
        let table ← buildInitial i (by omega)
        let row ← initializeRow ⟨i, by omega⟩ n (by omega)
        pure (table.push row)
  let rec buildStageRow (previous : Table) (pivot rowIndex : Fin n) :
      (j : Nat) → j ≤ n → TimeM Cost (Vector (WithTop Int) j)
    | 0, _ => pure #v[]
    | j + 1, hj => do
        let row ← buildStageRow previous pivot rowIndex j (by omega)
        TimeM.tick ⟨0, 1⟩
        let column : Fin n := ⟨j, by omega⟩
        let value := min (tableGet previous rowIndex column)
          (tableGet previous rowIndex pivot + tableGet previous pivot column)
        pure (row.push value)
  let rec buildStage (previous : Table) (pivot : Fin n) :
      (i : Nat) → i ≤ n → TimeM Cost (Vector (Vector (WithTop Int) n) i)
    | 0, _ => pure #v[]
    | i + 1, hi => do
        let table ← buildStage previous pivot i (by omega)
        let row ← buildStageRow previous pivot ⟨i, by omega⟩ n (by omega)
        pure (table.push row)
  let rec runStages (initial : Table) : (k : Nat) → k ≤ n → TimeM Cost Table
    | 0, _ => pure initial
    | k + 1, hk => do
        let previous ← runStages initial k (by omega)
        buildStage previous ⟨k, by omega⟩ n (by omega)
  do
    let initial ← buildInitial n (by omega)
    let final ← runStages initial n (by omega)
    pure fun i j => tableGet final i j

/-- Report whether an extended-integer matrix has a negative diagonal entry. -/
def hasNegativeDiagonal {n : Nat} (distance : Fin n → Fin n → WithTop Int) : Bool :=
  (List.finRange n).any fun vertex => decide (distance vertex vertex < 0)

@[simp] private lemma zero_initializations : (0 : Cost).initializations = 0 := rfl
@[simp] private lemma zero_transitions : (0 : Cost).transitions = 0 := rfl

@[simp] private lemma add_initializations (left right : Cost) :
    (left + right).initializations = left.initializations + right.initializations := rfl

@[simp] private lemma add_transitions (left right : Cost) :
    (left + right).transitions = left.transitions + right.transitions := rfl

private lemma initializeRow_initializations {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (rowIndex : Fin n)
    (j : Nat) (hj : j ≤ n) :
    (floydWarshall.initializeRow weight rowIndex j hj).time.initializations = j := by
  induction j with
  | zero => simp [floydWarshall.initializeRow]
  | succ j ih =>
      simp only [floydWarshall.initializeRow, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_pure, add_initializations, zero_initializations]
      rw [ih (by omega)]

private lemma initializeRow_transitions {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (rowIndex : Fin n)
    (j : Nat) (hj : j ≤ n) :
    (floydWarshall.initializeRow weight rowIndex j hj).time.transitions = 0 := by
  induction j with
  | zero => simp [floydWarshall.initializeRow]
  | succ j ih =>
      simp only [floydWarshall.initializeRow, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_pure, add_transitions, zero_transitions]
      rw [ih (by omega)]

private lemma buildInitial_initializations {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (i : Nat) (hi : i ≤ n) :
    (floydWarshall.buildInitial weight i hi).time.initializations = i * n := by
  induction i with
  | zero => simp [floydWarshall.buildInitial]
  | succ i ih =>
      simp only [floydWarshall.buildInitial, TimeM.time_bind, TimeM.time_pure,
        add_initializations, zero_initializations]
      rw [ih (by omega), initializeRow_initializations]
      simp [Nat.succ_mul]

private lemma buildInitial_transitions {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (i : Nat) (hi : i ≤ n) :
    (floydWarshall.buildInitial weight i hi).time.transitions = 0 := by
  induction i with
  | zero => simp [floydWarshall.buildInitial]
  | succ i ih =>
      simp only [floydWarshall.buildInitial, TimeM.time_bind, TimeM.time_pure,
        add_transitions, zero_transitions]
      rw [ih (by omega), initializeRow_transitions]

private lemma buildStageRow_initializations {n : Nat}
    (tableGet : Vector (Vector (WithTop Int) n) n → Fin n → Fin n → WithTop Int)
    (previous : Vector (Vector (WithTop Int) n) n) (pivot rowIndex : Fin n)
    (j : Nat) (hj : j ≤ n) :
    (floydWarshall.buildStageRow tableGet previous pivot rowIndex j hj).time.initializations =
      0 := by
  induction j with
  | zero => simp [floydWarshall.buildStageRow]
  | succ j ih =>
      simp only [floydWarshall.buildStageRow, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_pure, add_initializations, zero_initializations]
      rw [ih (by omega)]

private lemma buildStageRow_transitions {n : Nat}
    (tableGet : Vector (Vector (WithTop Int) n) n → Fin n → Fin n → WithTop Int)
    (previous : Vector (Vector (WithTop Int) n) n) (pivot rowIndex : Fin n)
    (j : Nat) (hj : j ≤ n) :
    (floydWarshall.buildStageRow tableGet previous pivot rowIndex j hj).time.transitions = j := by
  induction j with
  | zero => simp [floydWarshall.buildStageRow]
  | succ j ih =>
      simp only [floydWarshall.buildStageRow, TimeM.time_bind, TimeM.time_tick,
        TimeM.time_pure, add_transitions, zero_transitions]
      rw [ih (by omega)]

private lemma buildStage_initializations {n : Nat}
    (tableGet : Vector (Vector (WithTop Int) n) n → Fin n → Fin n → WithTop Int)
    (previous : Vector (Vector (WithTop Int) n) n) (pivot : Fin n)
    (i : Nat) (hi : i ≤ n) :
    (floydWarshall.buildStage tableGet previous pivot i hi).time.initializations = 0 := by
  induction i with
  | zero => simp [floydWarshall.buildStage]
  | succ i ih =>
      simp only [floydWarshall.buildStage, TimeM.time_bind, TimeM.time_pure,
        add_initializations, zero_initializations]
      rw [ih (by omega), buildStageRow_initializations]

private lemma buildStage_transitions {n : Nat}
    (tableGet : Vector (Vector (WithTop Int) n) n → Fin n → Fin n → WithTop Int)
    (previous : Vector (Vector (WithTop Int) n) n) (pivot : Fin n)
    (i : Nat) (hi : i ≤ n) :
    (floydWarshall.buildStage tableGet previous pivot i hi).time.transitions = i * n := by
  induction i with
  | zero => simp [floydWarshall.buildStage]
  | succ i ih =>
      simp only [floydWarshall.buildStage, TimeM.time_bind, TimeM.time_pure,
        add_transitions, zero_transitions]
      rw [ih (by omega), buildStageRow_transitions]
      simp [Nat.succ_mul]

private lemma runStages_initializations {n : Nat}
    (tableGet : Vector (Vector (WithTop Int) n) n → Fin n → Fin n → WithTop Int)
    (initial : Vector (Vector (WithTop Int) n) n) (k : Nat) (hk : k ≤ n) :
    (floydWarshall.runStages tableGet initial k hk).time.initializations = 0 := by
  induction k with
  | zero => simp [floydWarshall.runStages]
  | succ k ih =>
      simp only [floydWarshall.runStages, TimeM.time_bind, add_initializations]
      rw [ih (by omega), buildStage_initializations]

private lemma runStages_transitions {n : Nat}
    (tableGet : Vector (Vector (WithTop Int) n) n → Fin n → Fin n → WithTop Int)
    (initial : Vector (Vector (WithTop Int) n) n) (k : Nat) (hk : k ≤ n) :
    (floydWarshall.runStages tableGet initial k hk).time.transitions = k * n ^ 2 := by
  induction k with
  | zero => simp [floydWarshall.runStages]
  | succ k ih =>
      simp only [floydWarshall.runStages, TimeM.time_bind, add_transitions]
      rw [ih (by omega), buildStage_transitions]
      simp [Nat.succ_mul, pow_two]

/-- Floyd-Warshall initializes exactly one cell for each ordered vertex pair. -/
theorem floydWarshall_initializations {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.initializations = n ^ 2 := by
  simp only [floydWarshall, TimeM.time_bind, TimeM.time_pure, add_initializations,
    zero_initializations]
  rw [buildInitial_initializations, runStages_initializations]
  simp [pow_two]

/-- Floyd-Warshall executes exactly one transition for each `(k, i, j)` triple. -/
theorem floydWarshall_transitions {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.transitions = n ^ 3 := by
  simp only [floydWarshall, TimeM.time_bind, TimeM.time_pure, add_transitions,
    zero_transitions]
  rw [buildInitial_transitions, runStages_transitions]
  simp [pow_succ, Nat.mul_assoc]

/-- The total abstract event count is `n^2 + n^3`. -/
theorem floydWarshall_time {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.total = n ^ 2 + n ^ 3 := by
  rw [Cost.total, floydWarshall_initializations, floydWarshall_transitions]

/-- The Boolean detector is true exactly when some diagonal entry is negative. -/
theorem hasNegativeDiagonal_eq_true_iff {n : Nat}
    (distance : Fin n → Fin n → WithTop Int) :
    hasNegativeDiagonal distance = true ↔ ∃ vertex, distance vertex vertex < 0 := by
  rw [hasNegativeDiagonal, List.any_eq_true]
  constructor
  · rintro ⟨vertex, _, negative⟩
    exact ⟨vertex, of_decide_eq_true negative⟩
  · rintro ⟨vertex, negative⟩
    exact ⟨vertex, List.mem_finRange vertex, decide_eq_true negative⟩

end Cslib.Algorithms.Lean.FloydWarshall
