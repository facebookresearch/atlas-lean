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

/-- **Weight of a vertex path in an extended-integer weight matrix.** Let $w$ assign to each
ordered pair of vertices in $\{0, \dots, n-1\}$ a weight in $\mathbb{Z} \cup \{\infty\}$. The
weight of a list of vertices $v_0, v_1, \dots, v_m$ with $m \ge 1$ is
$w(v_0, v_1) + w(v_1, v_2) + \cdots + w(v_{m-1}, v_m)$, computed in $\mathbb{Z} \cup \{\infty\}$
where adding $\infty$ gives $\infty$. The empty list and every single-vertex list have
weight $0$. -/
def pathWeight {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    List (Fin n) → WithTop Int
  | [] => 0
  | [_] => 0
  | source :: target :: rest =>
      weight source target + pathWeight weight (target :: rest)

/-- **Finite-weight vertex path in a weight matrix.** Let $w$ assign to each ordered pair of
vertices in $\{0, \dots, n-1\}$ a weight in $\mathbb{Z} \cup \{\infty\}$, and let $s$ and $t$ be
vertices. A list of vertices $p$ is a weighted path from $s$ to $t$ when $p$ is nonempty, its
first entry is $s$, its last entry is $t$, and $w(u, v) \ne \infty$ for every pair of consecutive
entries $u, v$ of $p$. -/
def IsWeightedPath {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (source target : Fin n) (path : List (Fin n)) : Prop :=
  path.IsChainFromTo (fun left right => weight left right ≠ ⊤) source target

/-- **Intermediate vertices below a bound.** For a natural number $k$, a list of vertices in
$\{0, \dots, n - 1\}$ has all its intermediate vertices below $k$ when every entry of the list
other than its first and its last is less than $k$. -/
def InternalVerticesBelow {n : Nat} (k : Nat) (path : List (Fin n)) : Prop :=
  ∀ vertex ∈ path.tail.dropLast, vertex.val < k

/-- **Stage-$k$ shortest-path weight.** Let $w$ assign to each ordered pair of vertices in
$\{0, \dots, n-1\}$ a weight in $\mathbb{Z} \cup \{\infty\}$, let $k$ be a natural number, let
$s$ and $t$ be vertices and let $d \in \mathbb{Z} \cup \{\infty\}$. A weighted path from $s$ to
$t$ is a nonempty list of vertices that starts at $s$, ends at $t$ and has $w(u, v) \ne \infty$
for every pair of consecutive vertices $u, v$; its weight is the sum of these values $w(u, v)$,
and its intermediate vertices are all its entries except the first and the last. Then $d$ is the
stage-$k$ shortest-path weight from $s$ to $t$ when $d$ is at most the weight of every weighted
path from $s$ to $t$ whose intermediate vertices are all less than $k$, and either $d = \infty$ or
some such path has weight exactly $d$. -/
def IsStageShortestPathWeight {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (k : Nat) (source target : Fin n) (distance : WithTop Int) : Prop :=
  (∀ path, IsWeightedPath weight source target path → InternalVerticesBelow k path →
    distance ≤ pathWeight weight path) ∧
  (distance = ⊤ ∨ ∃ path, IsWeightedPath weight source target path ∧
    InternalVerticesBelow k path ∧ pathWeight weight path = distance)

/-- **Negative cycles.** For an $n \times n$ matrix $w$ of weights in $\mathbb{Z} \cup \{+\infty\}$,
a list of vertices $v_0, \dots, v_m$ is a negative cycle when $m \ge 1$, $v_m = v_0$, every
weight $w_{v_i v_{i+1}}$ with $i < m$ is finite, the vertices $v_0, \dots, v_{m-1}$ are
pairwise distinct, and the path weight $\sum_{i < m} w_{v_i v_{i+1}}$ is negative. -/
def IsNegativeCycle {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (cycle : List (Fin n)) : Prop :=
  ∃ base, IsWeightedPath weight base base cycle ∧ 2 ≤ cycle.length ∧
    cycle.dropLast.Nodup ∧ pathWeight weight cycle < 0

/-- **Matrices with a negative cycle.** An $n \times n$ matrix $w$ of weights in
$\mathbb{Z} \cup \{+\infty\}$ has a negative cycle when some list of vertices is a negative
cycle for $w$. -/
def HasNegativeCycle {n : Nat} (weight : Fin n → Fin n → WithTop Int) : Prop :=
  ∃ cycle, IsNegativeCycle weight cycle

/-- **Weight matrices without negative cycles.** Let $w$ assign to each ordered pair of vertices
in $\{0, \dots, n-1\}$ a weight in $\mathbb{Z} \cup \{\infty\}$. Then $w$ has no negative cycle
when there is no list of vertices $v_0, v_1, \dots, v_m$ with $m \ge 1$ such that $v_m = v_0$,
the vertices $v_0, \dots, v_{m-1}$ are pairwise distinct, $w(v_{i-1}, v_i) \ne \infty$ for
$1 \le i \le m$, and $w(v_0, v_1) + \cdots + w(v_{m-1}, v_m) < 0$. -/
def NoNegativeCycle {n : Nat} (weight : Fin n → Fin n → WithTop Int) : Prop :=
  ¬HasNegativeCycle weight

/-- **Floyd–Warshall cost record.** A cost record for the Floyd–Warshall algorithm is a pair of
natural numbers: the number of initialization events (input matrix cells copied into the initial
distance table) and the number of min-plus transition events (table entries updated). -/
structure Cost where
  /-- Input matrix cells copied and diagonal-normalized. -/
  initializations : Nat
  /-- Executed min-plus table transitions. -/
  transitions : Nat
deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩

instance : Add Cost := ⟨fun left right =>
  ⟨left.initializations + right.initializations, left.transitions + right.transitions⟩⟩

/-- **Total Floyd–Warshall cost.** The total of a Floyd–Warshall cost record is its number of
initialization events plus its number of min-plus transition events. -/
def Cost.total (cost : Cost) : Nat := cost.initializations + cost.transitions

/-- **Floyd–Warshall algorithm.** Given an $n \times n$ matrix $w$ of weights in
$\mathbb{Z} \cup \{+\infty\}$ indexed by the vertices $0, \dots, n - 1$, the Floyd–Warshall
algorithm starts from the table with $d^{(0)}_{ii} = \min(w_{ii}, 0)$ and $d^{(0)}_{ij} = w_{ij}$
for $i \ne j$, and for $k = 0, \dots, n - 1$ computes the table
$d^{(k+1)}_{ij} = \min\bigl(d^{(k)}_{ij}, d^{(k)}_{ik} + d^{(k)}_{kj}\bigr)$. It returns the
matrix $d^{(n)}$ together with its cost: one initialization event for each entry of $d^{(0)}$
and one transition event for each entry of each table $d^{(k+1)}$. -/
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

/-- **Negative-diagonal test.** For an $n \times n$ matrix $d$ with entries in
$\mathbb{Z} \cup \{+\infty\}$, the negative-diagonal test on $d$ is the Boolean value that is
true exactly when $d_{vv} < 0$ for some vertex $v$. -/
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

/-- **Initialization count of Floyd–Warshall.** For every $n$ and every $n \times n$ matrix of
weights in $\mathbb{Z} \cup \{+\infty\}$, the Floyd–Warshall algorithm performs exactly $n^2$
initialization events, one for each ordered pair of vertices. -/
theorem floydWarshall_initializations {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.initializations = n ^ 2 := by
  simp only [floydWarshall, TimeM.time_bind, TimeM.time_pure, add_initializations,
    zero_initializations]
  rw [buildInitial_initializations, runStages_initializations]
  simp [pow_two]

/-- **Transition count of Floyd–Warshall.** For every $n$ and every $n \times n$ matrix of weights
in $\mathbb{Z} \cup \{+\infty\}$, the Floyd–Warshall algorithm performs exactly $n^3$ min-plus
transition events, one for each triple $(k, i, j)$ of vertices. -/
theorem floydWarshall_transitions {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.transitions = n ^ 3 := by
  simp only [floydWarshall, TimeM.time_bind, TimeM.time_pure, add_transitions,
    zero_transitions]
  rw [buildInitial_transitions, runStages_transitions]
  simp [pow_succ, Nat.mul_assoc]

/-- **Floyd–Warshall performs $n^2 + n^3$ steps.** For every $n$ and every $n \times n$ matrix of
weights in $\mathbb{Z} \cup \{+\infty\}$, the total number of events counted by the Floyd–Warshall
algorithm, initialization events plus min-plus transition events, is exactly $n^2 + n^3$. -/
theorem floydWarshall_time {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (floydWarshall weight).time.total = n ^ 2 + n ^ 3 := by
  rw [Cost.total, floydWarshall_initializations, floydWarshall_transitions]

/-- **Characterization of the negative-diagonal test.** For every $n \times n$ matrix $d$ with
entries in $\mathbb{Z} \cup \{+\infty\}$, the negative-diagonal test on $d$ returns true if and
only if $d_{vv} < 0$ for some vertex $v$. -/
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
