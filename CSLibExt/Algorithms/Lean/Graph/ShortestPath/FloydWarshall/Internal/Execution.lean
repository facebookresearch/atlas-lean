/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic
import Batteries.Data.Vector.Lemmas

/-!
# Floyd-Warshall execution lemmas

Internal lookup equations connecting the tick-bearing vector loops to the mathematical stage
recurrence. This module is proof plumbing and is not re-exported by the public facade.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall.Internal

abbrev Table (n : Nat) := Vector (Vector (WithTop Int) n) n

def tableGet {n : Nat} (table : Table n) (i j : Fin n) : WithTop Int :=
  (table.get i).get j

def initialValue {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (i j : Fin n) : WithTop Int :=
  min (weight i j) (if i = j then 0 else ⊤)

def stageValue {n : Nat} (weight : Fin n → Fin n → WithTop Int) :
    (k : Nat) → k ≤ n → Fin n → Fin n → WithTop Int
  | 0, _, i, j => initialValue weight i j
  | k + 1, hk, i, j =>
      let pivot : Fin n := ⟨k, by omega⟩
      min (stageValue weight k (by omega) i j)
        (stageValue weight k (by omega) i pivot +
          stageValue weight k (by omega) pivot j)

lemma initializeRow_get {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (rowIndex : Fin n) (j : Nat) (hj : j ≤ n) (column : Fin j) :
    (floydWarshall.initializeRow weight rowIndex j hj).ret.get column =
      initialValue weight rowIndex (Fin.castLE hj column) := by
  induction j with
  | zero => exact Fin.elim0 column
  | succ j ih =>
      simp only [floydWarshall.initializeRow, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hcolumn : column.val < j
      · let previous : Fin j := ⟨column.val, hcolumn⟩
        have hcolumnEq : column = previous.castSucc := Fin.ext rfl
        rw [hcolumnEq, Vector.get_push_castSucc]
        have hprevious := ih (by omega) previous
        have hcast : Fin.castLE (by omega) previous =
            Fin.castLE hj previous.castSucc := Fin.ext rfl
        rw [← hcast]
        exact hprevious
      · have hval : column.val = j := by omega
        have hcolumnEq : column = Fin.last j := Fin.ext hval
        rw [hcolumnEq, Vector.get_push_last]
        have hcast : (⟨j, by omega⟩ : Fin n) = Fin.castLE hj (Fin.last j) := Fin.ext rfl
        rw [← hcast]
        rfl

lemma buildInitial_get {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (i : Nat) (hi : i ≤ n) (row : Fin i) (column : Fin n) :
    ((floydWarshall.buildInitial weight i hi).ret.get row).get column =
      initialValue weight (Fin.castLE hi row) column := by
  induction i with
  | zero => exact Fin.elim0 row
  | succ i ih =>
      simp only [floydWarshall.buildInitial, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hrow : row.val < i
      · let previous : Fin i := ⟨row.val, hrow⟩
        have hrowEq : row = previous.castSucc := Fin.ext rfl
        rw [hrowEq, Vector.get_push_castSucc]
        have hprevious := ih (by omega) previous
        have hcast : Fin.castLE (by omega) previous =
            Fin.castLE hi previous.castSucc := Fin.ext rfl
        rw [← hcast]
        exact hprevious
      · have hval : row.val = i := by omega
        have hrowEq : row = Fin.last i := Fin.ext hval
        rw [hrowEq, Vector.get_push_last]
        have hcell := initializeRow_get weight (⟨i, by omega⟩ : Fin n) n (by omega) column
        have hcast : (⟨i, by omega⟩ : Fin n) = Fin.castLE hi (Fin.last i) := Fin.ext rfl
        rw [← hcast]
        exact hcell

lemma buildStageRow_get {n : Nat}
    (lookup : Table n → Fin n → Fin n → WithTop Int) (previous : Table n)
    (pivot rowIndex : Fin n) (j : Nat) (hj : j ≤ n) (column : Fin j) :
    (floydWarshall.buildStageRow lookup previous pivot rowIndex j hj).ret.get column =
      min (lookup previous rowIndex (Fin.castLE hj column))
        (lookup previous rowIndex pivot + lookup previous pivot (Fin.castLE hj column)) := by
  induction j with
  | zero => exact Fin.elim0 column
  | succ j ih =>
      simp only [floydWarshall.buildStageRow, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hcolumn : column.val < j
      · let prior : Fin j := ⟨column.val, hcolumn⟩
        have hcolumnEq : column = prior.castSucc := Fin.ext rfl
        rw [hcolumnEq, Vector.get_push_castSucc]
        have hprior := ih (by omega) prior
        have hcast : Fin.castLE (by omega) prior =
            Fin.castLE hj prior.castSucc := Fin.ext rfl
        rw [← hcast]
        exact hprior
      · have hval : column.val = j := by omega
        have hcolumnEq : column = Fin.last j := Fin.ext hval
        rw [hcolumnEq, Vector.get_push_last]
        have hcast : (⟨j, by omega⟩ : Fin n) = Fin.castLE hj (Fin.last j) := Fin.ext rfl
        rw [← hcast]

lemma buildStage_get {n : Nat}
    (lookup : Table n → Fin n → Fin n → WithTop Int) (previous : Table n)
    (pivot : Fin n) (i : Nat) (hi : i ≤ n) (row : Fin i) (column : Fin n) :
    ((floydWarshall.buildStage lookup previous pivot i hi).ret.get row).get column =
      min (lookup previous (Fin.castLE hi row) column)
        (lookup previous (Fin.castLE hi row) pivot + lookup previous pivot column) := by
  induction i with
  | zero => exact Fin.elim0 row
  | succ i ih =>
      simp only [floydWarshall.buildStage, TimeM.ret_bind, TimeM.ret_pure]
      by_cases hrow : row.val < i
      · let prior : Fin i := ⟨row.val, hrow⟩
        have hrowEq : row = prior.castSucc := Fin.ext rfl
        rw [hrowEq, Vector.get_push_castSucc]
        have hprior := ih (by omega) prior
        have hcast : Fin.castLE (by omega) prior =
            Fin.castLE hi prior.castSucc := Fin.ext rfl
        rw [← hcast]
        exact hprior
      · have hval : row.val = i := by omega
        have hrowEq : row = Fin.last i := Fin.ext hval
        rw [hrowEq, Vector.get_push_last]
        have hcell := buildStageRow_get lookup previous pivot (⟨i, by omega⟩ : Fin n)
          n (by omega) column
        have hcast : (⟨i, by omega⟩ : Fin n) = Fin.castLE hi (Fin.last i) := Fin.ext rfl
        rw [← hcast]
        exact hcell

lemma runStages_get {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (initial : Table n)
    (hinitial : ∀ i j, tableGet initial i j = initialValue weight i j)
    (k : Nat) (hk : k ≤ n) (i j : Fin n) :
    tableGet (floydWarshall.runStages tableGet initial k hk).ret i j =
      stageValue weight k hk i j := by
  induction k generalizing i j with
  | zero => simpa [floydWarshall.runStages, stageValue] using hinitial i j
  | succ k ih =>
      simp only [floydWarshall.runStages, TimeM.ret_bind, tableGet]
      rw [buildStage_get]
      have hiCast : Fin.castLE (by omega) i = i := Fin.ext rfl
      rw [hiCast]
      let pivot : Fin n := ⟨k, by omega⟩
      rw [ih (by omega) i j, ih (by omega) i pivot, ih (by omega) pivot j]
      rfl

lemma floydWarshall_ret {n : Nat} (weight : Fin n → Fin n → WithTop Int)
    (i j : Fin n) :
    (floydWarshall weight).ret i j = stageValue weight n (by omega) i j := by
  simp only [floydWarshall, TimeM.ret_bind, TimeM.ret_pure]
  apply runStages_get weight _ _ n (by omega) i j
  intro row column
  simpa [tableGet] using buildInitial_get weight n (by omega) row column

end Cslib.Algorithms.Lean.FloydWarshall.Internal
