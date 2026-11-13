/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Cslib.Foundations.Data.List.IsChainFromTo
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic

/-!
# Boolean transitive closure

This is the saved-matrix dynamic program from CLRS4, Section 23.2.  One time unit is charged for
each cell assignment.  Matrix allocation, reads, equality tests, and Boolean operations are free
in this cost model.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TransitiveClosure

open Cslib.Algorithms.Lean

private def initializeRow {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (rowIndex : Fin n) : (columns : Nat) → columns ≤ n → TimeM Nat (Vector Bool columns)
  | 0, _ => pure #v[]
  | columns + 1, hcolumns => do
      let row ← initializeRow adjacency rowIndex columns (by omega)
      TimeM.tick 1
      let column : Fin n := ⟨columns, by omega⟩
      pure (row.push (decide (rowIndex = column) || adjacency rowIndex column))

private def buildInitial {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    (rows : Nat) → rows ≤ n → TimeM Nat (Vector (Vector Bool n) rows)
  | 0, _ => pure #v[]
  | rows + 1, hrows => do
      let table ← buildInitial adjacency rows (by omega)
      let row ← initializeRow adjacency ⟨rows, by omega⟩ n (by omega)
      pure (table.push row)

private def buildStageRow {n : Nat} (previous : Vector (Vector Bool n) n)
    (pivot rowIndex : Fin n) :
    (columns : Nat) → columns ≤ n → TimeM Nat (Vector Bool columns)
  | 0, _ => pure #v[]
  | columns + 1, hcolumns => do
      let row ← buildStageRow previous pivot rowIndex columns (by omega)
      TimeM.tick 1
      let column : Fin n := ⟨columns, by omega⟩
      let value := (previous.get rowIndex).get column ||
        ((previous.get rowIndex).get pivot && (previous.get pivot).get column)
      pure (row.push value)

private def buildStage {n : Nat} (previous : Vector (Vector Bool n) n) (pivot : Fin n) :
    (rows : Nat) → rows ≤ n → TimeM Nat (Vector (Vector Bool n) rows)
  | 0, _ => pure #v[]
  | rows + 1, hrows => do
      let table ← buildStage previous pivot rows (by omega)
      let row ← buildStageRow previous pivot ⟨rows, by omega⟩ n (by omega)
      pure (table.push row)

private def runStages {n : Nat} (initial : Vector (Vector Bool n) n) :
    (pivots : Nat) → pivots ≤ n → TimeM Nat (Vector (Vector Bool n) n)
  | 0, _ => pure initial
  | pivots + 1, hpivots => do
      let previous ← runStages initial pivots (by omega)
      buildStage previous ⟨pivots, by omega⟩ n (by omega)

/-- **Staged transitive-closure computation.** Let $A$ be a Boolean adjacency matrix on the
vertices $0, \dots, n-1$ and let $k \le n$. The computation first builds the $n \times n$ Boolean
matrix $T^{(0)}$ whose entry $(i, j)$ is true exactly when $i = j$ or $A_{ij}$ is true. Then, for
$p = 0, \dots, k - 1$, it builds a new matrix $T^{(p+1)}$ from the saved matrix $T^{(p)}$ by
$T^{(p+1)}_{ij} = T^{(p)}_{ij} \lor (T^{(p)}_{ip} \land T^{(p)}_{pj})$, and it returns $T^{(k)}$.
One time unit is charged for each cell assignment. -/
@[no_expose]
def transitiveClosureStages {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (pivots : Nat) (hpivots : pivots ≤ n) : TimeM Nat (Vector (Vector Bool n) n) := do
  let initial ← buildInitial adjacency n (by omega)
  runStages initial pivots hpivots

/-- **Saved-matrix transitive-closure algorithm.** Given a Boolean adjacency matrix $A$ on the
vertices $0, 1, \dots, n-1$, the algorithm first builds the matrix $t^{(0)}$ with $t^{(0)}_{ij}$
true exactly when $i = j$ or $A_{ij}$ is true. Then, for $k = 0, 1, \dots, n-1$ in turn, it
builds a new matrix $t^{(k+1)}$ with
$t^{(k+1)}_{ij} = t^{(k)}_{ij} \lor (t^{(k)}_{ik} \land t^{(k)}_{kj})$ for all $i, j$, reading
every operand from the saved matrix $t^{(k)}$, and it returns $t^{(n)}$. One time unit is
charged for each cell assignment; reads, Boolean operations and matrix allocation are free.

This is the saved-matrix recurrence of CLRS for the reflexive transitive closure. -/
@[no_expose]
def transitiveClosure {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    TimeM Nat (Fin n → Fin n → Bool) := do
  let final ← transitiveClosureStages adjacency n (by omega)
  pure fun i j => (final.get i).get j

private lemma initializeRow_ret {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (rowIndex : Fin n) (columns : Nat) (hcolumns : columns ≤ n)
    (column : Nat) (hcolumn : column < columns) :
    (initializeRow adjacency rowIndex columns hcolumns).ret[column] =
      (decide (rowIndex = (⟨column, by omega⟩ : Fin n)) ||
        adjacency rowIndex ⟨column, by omega⟩) := by
  induction columns with
  | zero => omega
  | succ columns ih =>
      simp only [initializeRow, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hlt : column < columns
      · rw [Vector.getElem_push_lt hlt]
        exact ih (by omega) hlt
      · have hcolumn' : column = columns := by omega
        subst column
        rw [Vector.getElem_push_eq]

private lemma initializeRow_time {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (rowIndex : Fin n) (columns : Nat) (hcolumns : columns ≤ n) :
    (initializeRow adjacency rowIndex columns hcolumns).time = columns := by
  induction columns with
  | zero => rfl
  | succ columns ih =>
      simp only [initializeRow, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      rw [ih (by omega)]
      omega

private lemma buildInitial_ret {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (rows : Nat) (hrows : rows ≤ n) (row column : Nat)
    (hrow : row < rows) (hcolumn : column < n) :
    ((buildInitial adjacency rows hrows).ret[row])[column] =
      (decide ((⟨row, by omega⟩ : Fin n) = ⟨column, by omega⟩) ||
        adjacency ⟨row, by omega⟩ ⟨column, by omega⟩) := by
  induction rows with
  | zero => omega
  | succ rows ih =>
      simp only [buildInitial, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hlt : row < rows
      · simp only [Vector.getElem_push_lt hlt]
        exact ih (by omega) hlt
      · have hrow' : row = rows := by omega
        subst row
        simp only [Vector.getElem_push_eq]
        exact initializeRow_ret adjacency ⟨rows, by omega⟩ n (by omega) column hcolumn

private lemma buildInitial_time {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (rows : Nat) (hrows : rows ≤ n) :
    (buildInitial adjacency rows hrows).time = rows * n := by
  induction rows with
  | zero => simp [buildInitial]
  | succ rows ih =>
      simp only [buildInitial, TimeM.time_bind, TimeM.time_pure]
      rw [ih (by omega), initializeRow_time]
      simp [Nat.add_mul]

private lemma buildStageRow_ret {n : Nat} (previous : Vector (Vector Bool n) n)
    (pivot rowIndex : Fin n) (columns : Nat) (hcolumns : columns ≤ n)
    (column : Nat) (hcolumn : column < columns) :
    (buildStageRow previous pivot rowIndex columns hcolumns).ret[column] =
      ((previous.get rowIndex).get ⟨column, by omega⟩ ||
        ((previous.get rowIndex).get pivot &&
          (previous.get pivot).get ⟨column, by omega⟩)) := by
  induction columns with
  | zero => omega
  | succ columns ih =>
      simp only [buildStageRow, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hlt : column < columns
      · rw [Vector.getElem_push_lt hlt]
        exact ih (by omega) hlt
      · have hcolumn' : column = columns := by omega
        subst column
        rw [Vector.getElem_push_eq]

private lemma buildStageRow_time {n : Nat} (previous : Vector (Vector Bool n) n)
    (pivot rowIndex : Fin n) (columns : Nat) (hcolumns : columns ≤ n) :
    (buildStageRow previous pivot rowIndex columns hcolumns).time = columns := by
  induction columns with
  | zero => rfl
  | succ columns ih =>
      simp only [buildStageRow, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      rw [ih (by omega)]
      omega

private lemma buildStage_ret {n : Nat} (previous : Vector (Vector Bool n) n)
    (pivot : Fin n) (rows : Nat) (hrows : rows ≤ n)
    (row column : Nat) (hrow : row < rows) (hcolumn : column < n) :
    ((buildStage previous pivot rows hrows).ret[row])[column] =
      ((previous.get ⟨row, by omega⟩).get ⟨column, by omega⟩ ||
        ((previous.get ⟨row, by omega⟩).get pivot &&
          (previous.get pivot).get ⟨column, by omega⟩)) := by
  induction rows with
  | zero => omega
  | succ rows ih =>
      simp only [buildStage, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hlt : row < rows
      · simp only [Vector.getElem_push_lt hlt]
        exact ih (by omega) hlt
      · have hrow' : row = rows := by omega
        subst row
        simp only [Vector.getElem_push_eq]
        exact buildStageRow_ret previous pivot ⟨rows, by omega⟩ n (by omega) column hcolumn

private lemma buildStage_time {n : Nat} (previous : Vector (Vector Bool n) n)
    (pivot : Fin n) (rows : Nat) (hrows : rows ≤ n) :
    (buildStage previous pivot rows hrows).time = rows * n := by
  induction rows with
  | zero => simp [buildStage]
  | succ rows ih =>
      simp only [buildStage, TimeM.time_bind, TimeM.time_pure]
      rw [ih (by omega), buildStageRow_time]
      simp [Nat.add_mul]

private lemma runStages_time {n : Nat} (initial : Vector (Vector Bool n) n)
    (pivots : Nat) (hpivots : pivots ≤ n) :
    (runStages initial pivots hpivots).time = pivots * n * n := by
  induction pivots with
  | zero => simp [runStages]
  | succ pivots ih =>
      simp only [runStages, TimeM.time_bind]
      rw [ih (by omega), buildStage_time]
      simp [Nat.add_mul]

/-- **Initial matrix of the transitive-closure computation.** Let $A$ be a Boolean adjacency
matrix on the vertices $0, \dots, n-1$. For all vertices $i$ and $j$, the entry $(i, j)$ of the
matrix produced by the staged transitive-closure computation with no pivot stages is true if and
only if $i = j$ or $A_{ij}$ is true. -/
theorem transitiveClosureStages_zero_cell {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (i j : Fin n) :
    ((transitiveClosureStages adjacency 0 (by omega)).ret.get i).get j =
      (decide (i = j) || adjacency i j) := by
  simp only [transitiveClosureStages, TimeM.ret_bind, runStages, TimeM.ret_pure]
  exact buildInitial_ret adjacency n (by omega) i.val j.val i.isLt j.isLt

/-- **Transition recurrence of the transitive-closure stages.** Let $A$ be a Boolean adjacency
matrix on the vertices $0, \dots, n-1$, and for $m \le n$ let $T^{(m)}$ be the matrix produced by
the staged transitive-closure computation on $A$ after its first $m$ pivot stages. For every
$k < n$ and all vertices $i$ and $j$,
$$T^{(k+1)}_{ij} = T^{(k)}_{ij} \lor \bigl(T^{(k)}_{ik} \land T^{(k)}_{kj}\bigr).$$

Every operand of stage $k + 1$ is read from the complete matrix saved after stage $k$. -/
theorem transitiveClosureStages_succ_cell {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (k : Nat) (hk : k < n) (i j : Fin n) :
    let previous := (transitiveClosureStages adjacency k (by omega)).ret
    ((transitiveClosureStages adjacency (k + 1) (by omega)).ret.get i).get j =
      ((previous.get i).get j ||
        ((previous.get i).get ⟨k, hk⟩ && (previous.get ⟨k, hk⟩).get j)) := by
  simp only [transitiveClosureStages, TimeM.ret_bind, runStages]
  exact buildStage_ret
    (runStages (buildInitial adjacency n (by omega)).ret k (by omega)).ret
    ⟨k, hk⟩ n (by omega) i.val j.val i.isLt j.isLt

private lemma transitiveClosureStages_time_raw {n : Nat}
    (adjacency : Fin n → Fin n → Bool) (pivots : Nat) (hpivots : pivots ≤ n) :
    (transitiveClosureStages adjacency pivots hpivots).time = n * n + pivots * n * n := by
  simp only [transitiveClosureStages, TimeM.time_bind]
  rw [buildInitial_time, runStages_time]

/-- **Cost of initializing the transitive-closure matrix.** For every Boolean adjacency matrix on
$n$ vertices, the staged transitive-closure computation with no pivot stages (only the
initialization of the $n \times n$ matrix) charges exactly $n^2$ time units, one for each cell
assignment. -/
theorem transitiveClosure_initializations {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    (transitiveClosureStages adjacency 0 (by omega)).time = n ^ 2 := by
  rw [transitiveClosureStages_time_raw]
  simp [pow_two]

/-- **Cost of one transition stage.** For every Boolean adjacency matrix on $n$ vertices and every
$k < n$, the time charged by the staged transitive-closure computation with $k + 1$ pivot stages
minus the time charged with $k$ pivot stages equals $n^2$: one time unit for each cell assignment
of the new stage. -/
theorem transitiveClosure_stage_assignments {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (k : Nat) (hk : k < n) :
    (transitiveClosureStages adjacency (k + 1) (by omega)).time -
        (transitiveClosureStages adjacency k (by omega)).time = n ^ 2 := by
  rw [transitiveClosureStages_time_raw, transitiveClosureStages_time_raw]
  simp [pow_two, Nat.add_sub_add_left, Nat.add_mul]

/-- **Cost of the transition stages of transitive closure.** Charge one time unit for each cell
assignment. For every Boolean adjacency matrix on $n$ vertices, let $a$ be the cost of running the
initialization of the saved-matrix transitive-closure algorithm followed by all $n$ of its
stages, and let $b$ be the cost of running the initialization alone. Then $a - b = n^3$, where the
subtraction is subtraction of natural numbers, truncated at $0$. That is, the $n$ transition
stages together perform exactly $n^3$ cell assignments. -/
theorem transitiveClosure_transition_assignments {n : Nat}
    (adjacency : Fin n → Fin n → Bool) :
    (transitiveClosureStages adjacency n (by omega)).time -
        (transitiveClosureStages adjacency 0 (by omega)).time = n ^ 3 := by
  rw [transitiveClosureStages_time_raw, transitiveClosureStages_time_raw]
  simp [pow_succ, Nat.mul_assoc]

private lemma internalVerticesBelow_mono {n k : Nat} {path : List (Fin n)}
    (hpath : FloydWarshall.InternalVerticesBelow k path) :
    FloydWarshall.InternalVerticesBelow (k + 1) path := by
  intro vertex hvertex
  exact Nat.lt_succ_of_lt (hpath vertex hvertex)

private lemma internalVerticesBelow_append_tail {n k : Nat} {r : Fin n → Fin n → Prop}
    {i pivot j : Fin n}
    {left right : List (Fin n)}
    (hpivot : pivot.val = k)
    (hleft : left.IsChainFromTo r i pivot)
    (hright : right.IsChainFromTo r pivot j)
    (hleftBelow : FloydWarshall.InternalVerticesBelow k left)
    (hrightBelow : FloydWarshall.InternalVerticesBelow k right) :
    FloydWarshall.InternalVerticesBelow (k + 1) (left ++ right.tail) := by
  intro vertex hvertex
  simp only [FloydWarshall.InternalVerticesBelow] at hleftBelow hrightBelow
  have hcases : vertex ∈ left.tail.dropLast ∨ vertex = pivot ∨
      vertex ∈ right.tail.dropLast := by
    cases left with
    | nil => exact False.elim (hleft.ne_nil rfl)
    | cons a as =>
      cases right with
      | nil => exact False.elim (hright.ne_nil rfl)
      | cons b bs =>
        have hb : b = pivot := hright.head_eq
        subst b
        simp only [List.cons_append, List.tail_cons] at hvertex
        by_cases hbs : bs = []
        · subst bs
          exact Or.inl (by simpa using hvertex)
        · have hmem : vertex ∈ as ∨ vertex ∈ bs.dropLast := by
            simpa [List.dropLast_append, hbs] using hvertex
          rcases hmem with hmem | hmem
          · cases as with
            | nil => simp at hmem
            | cons c cs =>
              have hlast : (c :: cs).getLast (by simp) = pivot := hleft.getLast_eq
              have hsplit : (c :: cs).dropLast ++ [pivot] = c :: cs :=
                hlast ▸ List.dropLast_append_getLast (by simp)
              rw [← hsplit] at hmem
              simp only [List.mem_append, List.mem_singleton] at hmem
              exact hmem.elim Or.inl (fun h => Or.inr (Or.inl h))
          · exact Or.inr (Or.inr hmem)
  rcases hcases with h | h | h
  · exact Nat.lt_succ_of_lt (hleftBelow vertex h)
  · subst vertex
    omega
  · exact Nat.lt_succ_of_lt (hrightBelow vertex h)

private lemma exists_nodup_below {n k : Nat} {adjacency : Fin n → Fin n → Bool}
    {i j : Fin n} {path : List (Fin n)}
    (hpath : path.IsChainFromTo (fun a b => adjacency a b = true) i j)
    (hbelow : FloydWarshall.InternalVerticesBelow k path) :
    ∃ simple, simple.IsChainFromTo (fun a b => adjacency a b = true) i j ∧
      simple.Nodup ∧ FloydWarshall.InternalVerticesBelow k simple := by
  let admissible := fun vertex : Fin n => vertex.val < k ∨ vertex = i ∨ vertex = j
  let restricted := fun a b : Fin n =>
    adjacency a b = true ∧ admissible a ∧ admissible b
  have hmembers : ∀ vertex ∈ path, admissible vertex := by
    intro vertex hmember
    cases path with
    | nil => exact False.elim (hpath.ne_nil rfl)
    | cons a as =>
      simp only [List.mem_cons] at hmember
      rcases hmember with hmember | hmember
      · exact Or.inr (Or.inl (hmember.trans hpath.head_eq))
      · cases as with
        | nil => simp at hmember
        | cons b bs =>
          have hlast : (b :: bs).getLast (by simp) = j := hpath.getLast_eq
          have hsplit : (b :: bs).dropLast ++ [j] = b :: bs :=
            hlast ▸ List.dropLast_append_getLast (by simp)
          rw [← hsplit] at hmember
          simp only [List.mem_append, List.mem_singleton] at hmember
          rcases hmember with hmember | hmember
          · exact Or.inl (hbelow vertex hmember)
          · exact Or.inr (Or.inr hmember)
  have hchain : path.IsChain restricted := by
    apply List.isChain_iff_getElem.mpr
    intro index hindex
    exact ⟨hpath.isChain.getElem index hindex,
      hmembers _ (List.getElem_mem (by omega)), hmembers _ (List.getElem_mem hindex)⟩
  have hrestricted : path.IsChainFromTo restricted i j :=
    ⟨hchain, hpath.ne_nil, hpath.head_eq, hpath.getLast_eq⟩
  obtain ⟨simple, hsimple, hnodup⟩ := hrestricted.exists_nodup
  have hsimplePath : simple.IsChainFromTo (fun a b => adjacency a b = true) i j :=
    ⟨hsimple.isChain.imp (fun _ _ h => h.1), hsimple.ne_nil,
      hsimple.head_eq, hsimple.getLast_eq⟩
  refine ⟨simple, hsimplePath, hnodup, ?_⟩
  intro vertex hvertex
  obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hvertex
  have hindex' : index + 2 < simple.length := by
    simp only [List.length_dropLast, List.length_tail] at hindex
    omega
  simp only [List.getElem_dropLast, List.getElem_tail] at hget
  have hstep := hsimple.isChain.getElem index (by omega)
  have hadmissible : admissible vertex := by
    simpa only [hget] using hstep.2.2
  have hneFirst : vertex ≠ i := by
    intro heq
    have hpositions : simple[index + 1] = simple[0]'hsimplePath.length_pos :=
      hget.trans (heq.trans hsimplePath.getElem_zero.symm)
    have := hnodup.getElem_inj.mp hpositions
    omega
  have hneLast : vertex ≠ j := by
    intro heq
    have hpositions : simple[index + 1] =
        simple[simple.length - 1]'(by have := hsimplePath.length_pos; omega) :=
      hget.trans (heq.trans hsimplePath.getElem_length_sub_one.symm)
    have := hnodup.getElem_inj.mp hpositions
    omega
  rcases hadmissible with hlt | hfirst | hlast
  · exact hlt
  · exact False.elim (hneFirst hfirst)
  · exact False.elim (hneLast hlast)

private lemma path_stage_zero_iff {n : Nat} (adjacency : Fin n → Fin n → Bool)
    (i j : Fin n) :
    (decide (i = j) || adjacency i j) = true ↔
      ∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) i j ∧
        FloydWarshall.InternalVerticesBelow 0 path := by
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | hedge
    · exact ⟨[i], List.isChainFromTo_singleton, by simp [FloydWarshall.InternalVerticesBelow]⟩
    · exact ⟨[i, j], by simpa using hedge, by simp [FloydWarshall.InternalVerticesBelow]⟩
  · rintro ⟨path, hpath, hbelow⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    have hempty : path.tail.dropLast = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro vertex hvertex
      exact Nat.not_lt_zero vertex.val (hbelow vertex hvertex)
    rcases path with _ | ⟨first, rest⟩
    · exact False.elim (hpath.ne_nil rfl)
    · rcases rest with _ | ⟨second, rest⟩
      · left
        exact hpath.head_eq.symm.trans hpath.getLast_eq
      · have hrest : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hlength := congrArg List.length hempty
          simp only [List.tail_cons, List.length_dropLast, List.length_cons,
            List.length_nil] at hlength
          omega
        subst rest
        right
        obtain ⟨hedge, rfl, rfl⟩ := List.isChainFromTo_pair_iff.mp hpath
        exact hedge

private lemma path_stage_succ_iff {n k : Nat} (hk : k < n)
    (adjacency : Fin n → Fin n → Bool) (i j : Fin n) :
    (∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) i j ∧
        FloydWarshall.InternalVerticesBelow (k + 1) path) ↔
      (∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) i j ∧
          FloydWarshall.InternalVerticesBelow k path) ∨
      ((∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) i ⟨k, hk⟩ ∧
          FloydWarshall.InternalVerticesBelow k path) ∧
        (∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) ⟨k, hk⟩ j ∧
          FloydWarshall.InternalVerticesBelow k path)) := by
  constructor
  · rintro ⟨path, hpath, hbelow⟩
    obtain ⟨simple, hsimple, hnodup, hsimpleBelow⟩ :=
      exists_nodup_below hpath hbelow
    by_cases hpivot : (⟨k, hk⟩ : Fin n) ∈ simple.tail.dropLast
    · obtain ⟨pivotOffset, hpivotOffset, hpivotGet⟩ := List.getElem_of_mem hpivot
      have hpivotBound : pivotOffset + 2 < simple.length := by
        simp only [List.length_dropLast, List.length_tail] at hpivotOffset
        omega
      simp only [List.getElem_dropLast, List.getElem_tail] at hpivotGet
      let pivotIndex := pivotOffset + 1
      have hpivotIndex : pivotIndex < simple.length := by dsimp [pivotIndex]; omega
      have hpivotInternal : 0 < pivotIndex ∧ pivotIndex + 1 < simple.length := by
        dsimp [pivotIndex]
        omega
      let left := simple.take (pivotIndex + 1)
      let right := simple.drop pivotIndex
      have hleft := hsimple.take hpivotIndex
      have hright := hsimple.drop hpivotIndex
      rw [hpivotGet] at hleft hright
      have hleftBelow : FloydWarshall.InternalVerticesBelow k left := by
        intro vertex hvertex
        obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hvertex
        have hleftIndex : index + 1 < pivotIndex := by
          simp only [List.length_dropLast, List.length_tail, List.length_take, left] at hindex
          omega
        simp only [List.getElem_dropLast, List.getElem_tail, left, List.getElem_take] at hget
        have hglobalIndex : index < simple.tail.dropLast.length := by
          simp only [List.length_dropLast, List.length_tail]
          omega
        have hglobalGet : simple.tail.dropLast[index] = vertex := by
          simpa only [List.getElem_dropLast, List.getElem_tail] using hget
        have hmember : vertex ∈ simple.tail.dropLast :=
          hglobalGet ▸ List.getElem_mem hglobalIndex
        have hne : vertex.val ≠ k := by
          intro heq
          have heq' : vertex = (⟨k, hk⟩ : Fin n) := Fin.ext heq
          have hpositions := hnodup.getElem_inj.mp (hget.trans (heq'.trans hpivotGet.symm))
          omega
        have hlt := hsimpleBelow vertex hmember
        omega
      have hrightBelow : FloydWarshall.InternalVerticesBelow k right := by
        intro vertex hvertex
        obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hvertex
        have hrightIndex : pivotIndex + index + 2 < simple.length := by
          simp only [List.length_dropLast, List.length_tail, List.length_drop, right] at hindex
          omega
        simp only [List.getElem_dropLast, List.getElem_tail, right, List.getElem_drop] at hget
        have hglobalIndex : pivotIndex + index < simple.tail.dropLast.length := by
          simp only [List.length_dropLast, List.length_tail]
          omega
        have hglobalGet : simple.tail.dropLast[pivotIndex + index] = vertex := by
          simpa only [List.getElem_dropLast, List.getElem_tail, Nat.add_assoc] using hget
        have hmember : vertex ∈ simple.tail.dropLast :=
          hglobalGet ▸ List.getElem_mem hglobalIndex
        have hne : vertex.val ≠ k := by
          intro heq
          have heq' : vertex = (⟨k, hk⟩ : Fin n) := Fin.ext heq
          have hpositions := hnodup.getElem_inj.mp (hget.trans (heq'.trans hpivotGet.symm))
          omega
        have hlt := hsimpleBelow vertex hmember
        omega
      exact Or.inr ⟨⟨left, hleft, hleftBelow⟩, ⟨right, hright, hrightBelow⟩⟩
    · left
      refine ⟨simple, hsimple, ?_⟩
      intro vertex hvertex
      have hlt := hsimpleBelow vertex hvertex
      have hne : vertex.val ≠ k := by
        intro heq
        apply hpivot
        have : vertex = (⟨k, hk⟩ : Fin n) := Fin.ext heq
        simpa [this] using hvertex
      omega
  · rintro (hkeep | ⟨hleft, hright⟩)
    · obtain ⟨path, hpath, hbelow⟩ := hkeep
      exact ⟨path, hpath, internalVerticesBelow_mono hbelow⟩
    · obtain ⟨left, hleft, hleftBelow⟩ := hleft
      obtain ⟨right, hright, hrightBelow⟩ := hright
      refine ⟨left ++ right.tail, hleft.append_tail hright, ?_⟩
      exact internalVerticesBelow_append_tail rfl hleft hright hleftBelow hrightBelow

/-- **Invariant of the transitive-closure stages.** Let $A$ be a Boolean adjacency matrix of a
directed graph on the vertices $0, \dots, n-1$ and let $k \le n$. For all vertices $i$ and $j$, the
entry $(i, j)$ of the matrix produced by the staged transitive-closure computation after its first
$k$ pivot stages is true if and only if there are vertices $i = v_0, v_1, \dots, v_m = j$ with
$m \ge 0$ such that each $A_{v_t v_{t+1}}$ is true and every intermediate vertex
$v_1, \dots, v_{m-1}$ is less than $k$. -/
theorem transitiveClosureStages_cell_eq_true_iff {n : Nat}
    (adjacency : Fin n → Fin n → Bool) (pivots : Nat) (hpivots : pivots ≤ n)
    (i j : Fin n) :
    ((transitiveClosureStages adjacency pivots hpivots).ret.get i).get j = true ↔
      ∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) i j ∧
        FloydWarshall.InternalVerticesBelow pivots path := by
  induction pivots generalizing i j with
  | zero =>
      rw [transitiveClosureStages_zero_cell]
      exact path_stage_zero_iff adjacency i j
  | succ pivots ih =>
      have hpivot : pivots < n := by omega
      rw [transitiveClosureStages_succ_cell adjacency pivots hpivot i j]
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      rw [ih (by omega), ih (by omega), ih (by omega)]
      exact (path_stage_succ_iff hpivot adjacency i j).symm

/-- **Correctness of the transitive-closure algorithm.** Let $A$ be a Boolean adjacency matrix
of a directed graph on the vertices $0, \dots, n-1$. For all vertices $i$ and $j$, the entry
$(i, j)$ of the matrix returned by the transitive-closure algorithm on $A$ is true if and only if
$j$ is reachable from $i$ by a sequence of zero or more edges of the graph. -/
theorem transitiveClosure_cell_eq_true_iff {n : Nat}
    (adjacency : Fin n → Fin n → Bool) (i j : Fin n) :
    (transitiveClosure adjacency).ret i j = true ↔
      Relation.ReflTransGen (fun a b => adjacency a b = true) i j := by
  rw [show (transitiveClosure adjacency).ret i j =
      ((transitiveClosureStages adjacency n (by omega)).ret.get i).get j by rfl]
  rw [transitiveClosureStages_cell_eq_true_iff]
  constructor
  · rintro ⟨path, hpath, _⟩
    exact hpath.reflTransGen
  · intro hreach
    obtain ⟨path, hne, hchain, hhead, hlast⟩ :=
      List.exists_isChain_ne_nil_of_relationReflTransGen hreach
    refine ⟨path, ⟨hchain, hne, hhead, hlast⟩, ?_⟩
    intro vertex _
    exact vertex.isLt

/-- **Running time of the transitive-closure algorithm.** For every Boolean adjacency matrix on
$n$ vertices, the transitive-closure algorithm charges exactly $n^2 + n^3$ time units: $n^2$ cell
assignments to initialize the matrix and $n^2$ in each of the $n$ transition stages. -/
theorem transitiveClosure_time {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    (transitiveClosure adjacency).time = n ^ 2 + n ^ 3 := by
  simp only [transitiveClosure, TimeM.time_bind, TimeM.time_pure]
  rw [transitiveClosureStages_time_raw]
  simp [pow_succ, Nat.mul_assoc]

/-- **Cost of transitive closure on the empty graph.** For the graph with no vertices, the
transitive-closure algorithm charges $0$ time units: it performs no cell assignments. -/
theorem transitiveClosure_time_zero (adjacency : Fin 0 → Fin 0 → Bool) :
    (transitiveClosure adjacency).time = 0 := by
  simpa using transitiveClosure_time adjacency

/-- **Cost of transitive closure on one vertex.** For every Boolean adjacency matrix on a single
vertex, the transitive-closure algorithm charges exactly $2$ time units: one cell assignment for
the initialization and one for the single transition stage. -/
theorem transitiveClosure_time_one (adjacency : Fin 1 → Fin 1 → Bool) :
    (transitiveClosure adjacency).time = 2 := by
  simpa using transitiveClosure_time adjacency

end Cslib.Algorithms.Lean.TransitiveClosure
