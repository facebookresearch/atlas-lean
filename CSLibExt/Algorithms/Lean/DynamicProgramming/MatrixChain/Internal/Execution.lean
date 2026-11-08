/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain.Basic
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Nat.Choose.Basic

/-!
# Matrix-chain execution internals

Table access, executable-loop aliases, and exact loop-event recurrences.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MatrixChain

open Cslib.Algorithms.Lean

namespace Internal

@[simp] theorem zero_candidateEvaluations :
    (0 : Cost).candidateEvaluations = 0 := rfl

@[simp] theorem zero_reconstructionNodes :
    (0 : Cost).reconstructionNodes = 0 := rfl

@[simp] theorem add_candidateEvaluations (left right : Cost) :
    (left + right).candidateEvaluations =
      left.candidateEvaluations + right.candidateEvaluations := rfl

@[simp] theorem add_reconstructionNodes (left right : Cost) :
    (left + right).reconstructionNodes =
      left.reconstructionNodes + right.reconstructionNodes := rfl

abbrev Cell (n : Nat) := Nat × (Option (Fin n) × Parenthesization n)

def Cell.cost {n : Nat} (cell : Cell n) : Nat := cell.1

def Cell.split {n : Nat} (cell : Cell n) : Option (Fin n) := cell.2.1

def Cell.witness {n : Nat} (cell : Cell n) : Parenthesization n := cell.2.2

abbrev Table (n : Nat) := Vector (Vector (Option (Cell n)) n) n

abbrev tableGet {n : Nat} (table : Table n) (i j : Fin n) : Option (Cell n) :=
  (table.get i).get j

abbrev tableSet {n : Nat} (table : Table n) (i j : Fin n)
    (value : Option (Cell n)) : Table n :=
  table.set i.val ((table.get i).set j.val value)

theorem tableGet_tableSet_self {n : Nat} (table : Table n) (i j : Fin n)
    (value : Option (Cell n)) : tableGet (tableSet table i j value) i j = value := by
  simp [tableGet, tableSet, Vector.get_eq_getElem]

theorem tableGet_tableSet_of_ne {n : Nat} (table : Table n)
    (i j p q : Fin n) (value : Option (Cell n)) (h : p ≠ i ∨ q ≠ j) :
    tableGet (tableSet table i j value) p q = tableGet table p q := by
  simp only [tableGet, tableSet, Vector.get_eq_getElem]
  by_cases hpi : p = i
  · subst p
    simp only [Vector.getElem_set_self]
    have hqj : q ≠ j := by tauto
    have hqjVal : q.val ≠ j.val := fun hEq => hqj (Fin.ext hEq)
    rw [Vector.getElem_set_ne j.isLt q.isLt (Ne.symm hqjVal)]
  · have hpiVal : p.val ≠ i.val := fun hEq => hpi (Fin.ext hEq)
    rw [Vector.getElem_set_ne i.isLt p.isLt (Ne.symm hpiVal)]

abbrev initialTable (n : Nat) : Table n :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if i = j then some (0, none, .matrix i) else none

def candidateTick : Cost := ⟨1, 0⟩

def reconstructionTick : Cost := ⟨0, 1⟩

abbrev scanSplits {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (i j : Fin n) :
    (count : Nat) → i.val + count ≤ j.val → TimeM Cost (Option (Cell n)) :=
  matrixChainOrderRaw.scanSplits dimensions tableGet table i j

abbrev fillStarts {n : Nat} (dimensions : Vector Nat (n + 1))
    (length : Nat) (hLength : 2 ≤ length) (hLengthN : length ≤ n) :
    (count : Nat) → count ≤ n - length + 1 → Table n → TimeM Cost (Table n) :=
  matrixChainOrderRaw.fillStarts dimensions (by omega) tableGet tableSet length hLength hLengthN

abbrev fillLengths {n : Nat} (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    (count : Nat) → count ≤ n - 1 → TimeM Cost (Table n) :=
  matrixChainOrderRaw.fillLengths dimensions hn tableGet tableSet (initialTable n)

def buildTable {n : Nat} (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    TimeM Cost (Table n) :=
  fillLengths dimensions hn (n - 1) (by omega)

lemma scanSplits_tie_retains_previous {n : Nat}
    (dimensions : Vector Nat (n + 1)) (table : Table n) (i j : Fin n)
    (count : Nat) (hCount : i.val + (count + 1) ≤ j.val)
    (current left right : Cell n)
    (hPrevious : (scanSplits dimensions table i j count (by omega)).ret = some current)
    (hLeft : tableGet table i ⟨i.val + count, by omega⟩ = some left)
    (hRight : tableGet table ⟨i.val + count + 1, by omega⟩ j = some right)
    (hTie : left.cost + right.cost +
      dimensions.get i.castSucc *
        dimensions.get ((⟨i.val + count, by omega⟩ : Fin n).succ) *
          dimensions.get j.succ = current.cost) :
    (scanSplits dimensions table i j (count + 1) hCount).ret = some current := by
  have hNotImprove : ¬(left.cost + right.cost +
      dimensions.get i.castSucc *
        dimensions.get ((⟨i.val + count, by omega⟩ : Fin n).succ) *
          dimensions.get j.succ) < current.cost := by
    rw [hTie]
    exact Nat.lt_irrefl _
  have hSucc : ((⟨i.val + count, by omega⟩ : Fin n).succ) =
      (⟨i.val + count + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hNotImproveRaw : ¬(left.1 + right.1 +
      dimensions.get i.castSucc *
        dimensions.get (⟨i.val + count + 1, by omega⟩ : Fin (n + 1)) *
          dimensions.get j.succ) < current.1 := by
    simpa only [Cell.cost, hSucc] using hNotImprove
  simp [scanSplits, matrixChainOrderRaw.scanSplits, hPrevious, hLeft, hRight,
    hNotImproveRaw]

def candidateCountFor (n : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      candidateCountFor n count + (n - (count + 2) + 1) * (count + 1)

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

def candidateCount : Nat → Nat
  | 0 => 0
  | n + 1 => candidateCount n + triangle n

@[simp] private theorem scanSplits_candidateEvaluations {n : Nat}
    (dimensions : Vector Nat (n + 1))
    (table : Table n) (i j : Fin n) (count : Nat) (hCount : i.val + count ≤ j.val) :
    (matrixChainOrderRaw.scanSplits dimensions tableGet table i j count
      hCount).time.candidateEvaluations = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [matrixChainOrderRaw.scanSplits, TimeM.time_bind,
        TimeM.time_tick]
      have hPrevious := ih (by omega)
      change
        (matrixChainOrderRaw.scanSplits dimensions tableGet table i j count
          _).time.candidateEvaluations = count at hPrevious
      rw [add_candidateEvaluations, hPrevious]
      simp

@[simp] private theorem scanSplits_reconstructionNodes {n : Nat}
    (dimensions : Vector Nat (n + 1))
    (table : Table n) (i j : Fin n) (count : Nat) (hCount : i.val + count ≤ j.val) :
    (matrixChainOrderRaw.scanSplits dimensions tableGet table i j count
      hCount).time.reconstructionNodes = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [matrixChainOrderRaw.scanSplits, TimeM.time_bind,
        TimeM.time_tick]
      have hPrevious := ih (by omega)
      change
        (matrixChainOrderRaw.scanSplits dimensions tableGet table i j count
          _).time.reconstructionNodes = 0 at hPrevious
      rw [add_reconstructionNodes, hPrevious]
      simp

theorem fillStarts_candidateEvaluations {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) (length : Nat)
    (hLength : 2 ≤ length) (hLengthN : length ≤ n)
    (count : Nat) (hCount : count ≤ n - length + 1) (table : Table n) :
    (matrixChainOrderRaw.fillStarts dimensions hn tableGet tableSet length hLength hLengthN
      count hCount table).time.candidateEvaluations = count * (length - 1) := by
  induction count generalizing table with
  | zero => simp [matrixChainOrderRaw.fillStarts]
  | succ count ih =>
      simp only [matrixChainOrderRaw.fillStarts, TimeM.time_bind, TimeM.time_pure]
      let previous := (matrixChainOrderRaw.fillStarts dimensions hn tableGet tableSet length
        hLength hLengthN count (by omega) table).ret
      let i : Fin n := ⟨count, by omega⟩
      let j : Fin n := ⟨count + length - 1, by omega⟩
      have hScan : i.val + (length - 1) ≤ j.val := by
        simp only [i, j]
        omega
      have hPrevious := ih (by omega) table
      rw [add_candidateEvaluations, hPrevious, add_candidateEvaluations,
        scanSplits_candidateEvaluations dimensions previous i j (length - 1),
        zero_candidateEvaluations]
      rw [Nat.succ_mul]
      simp

theorem fillStarts_reconstructionNodes {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) (length : Nat)
    (hLength : 2 ≤ length) (hLengthN : length ≤ n)
    (count : Nat) (hCount : count ≤ n - length + 1) (table : Table n) :
    (matrixChainOrderRaw.fillStarts dimensions hn tableGet tableSet length hLength hLengthN
      count hCount table).time.reconstructionNodes = 0 := by
  induction count generalizing table with
  | zero => simp [matrixChainOrderRaw.fillStarts]
  | succ count ih =>
      simp only [matrixChainOrderRaw.fillStarts, TimeM.time_bind, TimeM.time_pure]
      let previous := (matrixChainOrderRaw.fillStarts dimensions hn tableGet tableSet length
        hLength hLengthN count (by omega) table).ret
      let i : Fin n := ⟨count, by omega⟩
      let j : Fin n := ⟨count + length - 1, by omega⟩
      have hScan : i.val + (length - 1) ≤ j.val := by
        simp only [i, j]
        omega
      have hPrevious := ih (by omega) table
      rw [add_reconstructionNodes, hPrevious, add_reconstructionNodes,
        scanSplits_reconstructionNodes dimensions previous i j (length - 1),
        zero_reconstructionNodes]

theorem fillLengths_candidateEvaluations {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n)
    (count : Nat) (hCount : count ≤ n - 1) :
    (fillLengths dimensions hn count hCount).time.candidateEvaluations =
      candidateCountFor n count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [fillLengths, matrixChainOrderRaw.fillLengths, TimeM.time_bind,
        candidateCountFor]
      let previous := (fillLengths dimensions hn count (by omega)).ret
      let length := count + 2
      have hPrevious := ih (by omega)
      have hCurrent := fillStarts_candidateEvaluations dimensions hn length (by omega) (by omega)
        (n - length + 1) (by omega) previous
      change
        ((fillLengths dimensions hn count _).time +
          (fillStarts dimensions length (by omega) (by omega) (n - length + 1) _
            previous).time).candidateEvaluations = _
      rw [add_candidateEvaluations, hPrevious, hCurrent]
      rfl

theorem fillLengths_reconstructionNodes {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n)
    (count : Nat) (hCount : count ≤ n - 1) :
    (fillLengths dimensions hn count hCount).time.reconstructionNodes = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [fillLengths, matrixChainOrderRaw.fillLengths, TimeM.time_bind]
      let previous := (fillLengths dimensions hn count (by omega)).ret
      let length := count + 2
      have hPrevious := ih (by omega)
      have hCurrent := fillStarts_reconstructionNodes dimensions hn length (by omega) (by omega)
        (n - length + 1) (by omega) previous
      change
        ((fillLengths dimensions hn count _).time +
          (fillStarts dimensions length (by omega) (by omega) (n - length + 1) _
            previous).time).reconstructionNodes = _
      rw [add_reconstructionNodes, hPrevious, hCurrent]

theorem triangle_eq_choose (n : Nat) : triangle n = Nat.choose (n + 1) 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [triangle, ih]
      conv_rhs => rw [Nat.choose_succ_succ]
      simp [Nat.choose_one_right]
      omega

theorem candidateCount_eq_choose (n : Nat) :
    candidateCount n = Nat.choose (n + 1) 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [candidateCount, ih, triangle_eq_choose]
      conv_rhs => rw [Nat.choose_succ_succ]
      change (n + 1).choose 3 + (n + 1).choose 2 =
        (n + 1).choose 2 + (n + 1).choose 3
      omega

theorem candidateCountFor_succ (n count : Nat) (hCount : count ≤ n - 1) :
    candidateCountFor (n + 1) count = candidateCountFor n count + triangle count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [candidateCountFor, triangle]
      rw [ih (by omega)]
      have hSub : n + 1 - (count + 2) + 1 =
          (n - (count + 2) + 1) + 1 := by
        omega
      rw [hSub, Nat.add_mul]
      omega

theorem candidateCountFor_full (n : Nat) :
    candidateCountFor n (n - 1) = candidateCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [Nat.succ_sub_one]
          rw [candidateCountFor]
          rw [candidateCountFor_succ (n + 1) n (by omega)]
          have hPrevious : candidateCountFor (n + 1) n = candidateCount (n + 1) := by
            simpa only [Nat.succ_sub_one] using ih
          rw [hPrevious]
          simp only [candidateCount, triangle]
          have hCoefficient : n + 1 + 1 - (n + 2) + 1 = 1 := by omega
          rw [hCoefficient, Nat.one_mul]
          simp [Nat.add_assoc]

theorem triangle_le_square (n : Nat) : triangle n ≤ n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [triangle]
      calc
        triangle n + (n + 1) ≤ n ^ 2 + (n + 1) := Nat.add_le_add_right ih _
        _ ≤ (n + 1) ^ 2 := by
          simp only [pow_two, Nat.add_mul, Nat.mul_add]
          omega

theorem candidateCount_le_cube (n : Nat) : candidateCount n ≤ n ^ 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [candidateCount]
      calc
        candidateCount n + triangle n ≤ n ^ 3 + n ^ 2 :=
          Nat.add_le_add ih (triangle_le_square n)
        _ ≤ (n + 1) ^ 3 := by
          simp [pow_succ, Nat.add_mul, Nat.mul_add]
          omega

end Internal

end Cslib.Algorithms.Lean.MatrixChain
