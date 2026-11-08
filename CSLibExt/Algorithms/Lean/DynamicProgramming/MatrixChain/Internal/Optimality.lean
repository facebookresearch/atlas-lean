/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain.Internal.Execution

/-!
# Matrix-chain optimality internals

Interval semantics and the invariant proving each filled table cell is a realized minimum.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MatrixChain

open Cslib.Algorithms.Lean

namespace Internal

inductive IsInterval {n : Nat} : Nat → Nat → Parenthesization n → Prop
  | matrix (index : Fin n) : IsInterval index.val 1 (.matrix index)
  | multiply {start leftLength rightLength : Nat}
      {left right : Parenthesization n} :
      IsInterval start leftLength left →
      IsInterval (start + leftLength) rightLength right →
      IsInterval start (leftLength + rightLength) (.multiply left right)

theorem IsInterval.length_pos {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree) : 0 < length := by
  induction h with
  | matrix => simp
  | multiply _ _ ihLeft ihRight => omega

theorem IsInterval.end_le {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree) : start + length ≤ n := by
  induction h with
  | matrix index =>
      change Nat.succ index.val ≤ n
      exact Nat.succ_le_iff.mpr index.isLt
  | multiply hLeft hRight ihLeft ihRight => omega

theorem IsInterval.indices {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree) :
    tree.matrixIndices.map (fun index => index.val) = List.range' start length := by
  induction h with
  | matrix index => simp [Parenthesization.matrixIndices]
  | multiply hLeft hRight ihLeft ihRight =>
      simp only [Parenthesization.matrixIndices, List.map_append, ihLeft, ihRight]
      simp

theorem IsInterval.split_of_one_lt {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree) (hLength : 1 < length) :
    ∃ (leftLength rightLength : Nat) (leftTree rightTree : Parenthesization n),
      tree = .multiply leftTree rightTree ∧
        IsInterval start leftLength leftTree ∧
        IsInterval (start + leftLength) rightLength rightTree ∧
        leftLength + rightLength = length := by
  cases h with
  | matrix index => omega
  | @multiply start leftLength rightLength leftTree rightTree hLeft hRight =>
      exact ⟨leftLength, rightLength, leftTree, rightTree, rfl, hLeft, hRight, rfl⟩

theorem isInterval_of_indices {n start length : Nat}
    (tree : Parenthesization n)
    (hIndices : tree.matrixIndices.map (fun index => index.val) =
      List.range' start length) : IsInterval start length tree := by
  induction tree generalizing start length with
  | matrix index =>
      simp only [Parenthesization.matrixIndices, List.map_singleton] at hIndices
      have hLength : length = 1 := by
        simpa using (congrArg List.length hIndices).symm
      subst length
      simp only [List.range'_one, List.cons.injEq] at hIndices
      simpa [← hIndices.1] using IsInterval.matrix index
  | multiply left right ihLeft ihRight =>
      simp only [Parenthesization.matrixIndices, List.map_append] at hIndices
      obtain ⟨leftLength, hLength, hLeft, hRight⟩ :=
        List.range'_eq_append_iff.mp hIndices.symm
      have leftInterval := ihLeft hLeft
      have rightInterval := ihRight (by simpa using hRight)
      have combined := IsInterval.multiply leftInterval rightInterval
      simpa [Nat.add_sub_of_le hLength] using combined

theorem IsInterval.rows_eq {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree)
    (dimensions : Vector Nat (n + 1)) :
    tree.rows dimensions = dimensions.get ⟨start, by
      have hPos := h.length_pos
      have hEnd := h.end_le
      omega⟩ := by
  induction h with
  | matrix index =>
      simp only [Parenthesization.rows]
      congr 1
  | multiply hLeft hRight ihLeft ihRight =>
      simpa [Parenthesization.rows] using ihLeft

theorem IsInterval.cols_eq {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree)
    (dimensions : Vector Nat (n + 1)) :
    tree.cols dimensions = dimensions.get ⟨start + length, by
      have hEnd := h.end_le
      omega⟩ := by
  induction h with
  | matrix index =>
      simp only [Parenthesization.cols]
      congr 1
  | multiply hLeft hRight ihLeft ihRight =>
      simpa [Parenthesization.cols, Nat.add_assoc] using ihRight

theorem IsInterval.compatible {n start length : Nat}
    {tree : Parenthesization n} (h : IsInterval start length tree)
    (dimensions : Vector Nat (n + 1)) : tree.DimensionCompatible dimensions := by
  induction h with
  | matrix index => simp [Parenthesization.DimensionCompatible]
  | @multiply start leftLength rightLength left right hLeft hRight ihLeft ihRight =>
      refine ⟨ihLeft, ihRight, ?_⟩
      rw [hLeft.cols_eq dimensions, hRight.rows_eq dimensions]

def intervalLength {n : Nat} (i j : Fin n) : Nat :=
  j.val - i.val + 1

def CellOptimal {n : Nat} (dimensions : Vector Nat (n + 1))
    (i j : Fin n) (cell : Cell n) : Prop :=
  IsInterval i.val (intervalLength i j) cell.witness ∧
    scalarMultiplicationCost dimensions cell.witness = cell.cost ∧
    ∀ tree, IsInterval i.val (intervalLength i j) tree →
      cell.cost ≤ scalarMultiplicationCost dimensions tree

def CellSplitCorrect {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (i j : Fin n) (cell : Cell n) : Prop :=
  (i = j ∧ cell.split = none) ∨
    ∃ (k next : Fin n) (left right : Cell n),
      i.val ≤ k.val ∧ k.val < j.val ∧ cell.split = some k ∧
        next.val = k.val + 1 ∧
        tableGet table i k = some left ∧
        tableGet table next j = some right ∧
        cell.cost = left.cost + right.cost +
          dimensions.get i.castSucc * dimensions.get k.succ * dimensions.get j.succ ∧
        cell.witness = .multiply left.witness right.witness

def CellFirstAttainingSplit {n : Nat} (dimensions : Vector Nat (n + 1))
    (i j : Fin n) (cell : Cell n) : Prop :=
  (i = j ∧ cell.split = none) ∨
    ∀ {leftLength rightLength : Nat} {leftTree rightTree : Parenthesization n},
      IsInterval i.val leftLength leftTree →
      IsInterval (i.val + leftLength) rightLength rightTree →
      leftLength + rightLength = intervalLength i j →
      cell.cost = scalarMultiplicationCost dimensions (.multiply leftTree rightTree) →
      ∃ k, cell.split = some k ∧ k.val < i.val + leftLength

def TableCorrectThrough {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (maxLength : Nat) : Prop :=
  ∀ (i j : Fin n), i.val ≤ j.val → intervalLength i j ≤ maxLength →
    ∃ cell, tableGet table i j = some cell ∧
      CellOptimal dimensions i j cell ∧ CellSplitCorrect dimensions table i j cell ∧
        CellFirstAttainingSplit dimensions i j cell

theorem TableCorrectThrough.cell_firstAttainingSplit {n : Nat}
    (dimensions : Vector Nat (n + 1)) (table : Table n) (maxLength : Nat)
    (hTable : TableCorrectThrough dimensions table maxLength)
    (i j : Fin n) (hij : i.val ≤ j.val) (hLength : intervalLength i j ≤ maxLength)
    (cell : Cell n) (hGet : tableGet table i j = some cell) :
    CellFirstAttainingSplit dimensions i j cell := by
  obtain ⟨known, hKnown, hOptimal, hSplit, hFirst⟩ := hTable i j hij hLength
  have hKnownCell : known = cell := Option.some.inj (hKnown.symm.trans hGet)
  simpa only [hKnownCell] using hFirst

def PartialBestCorrect {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (i j : Fin n) (count : Nat) : Option (Cell n) → Prop
  | none => count = 0
  | some cell =>
      IsInterval i.val (intervalLength i j) cell.witness ∧
        scalarMultiplicationCost dimensions cell.witness = cell.cost ∧
        CellSplitCorrect dimensions table i j cell ∧
        (∃ k, cell.split = some k ∧ k.val < i.val + count) ∧
        ∀ {leftLength rightLength : Nat} {leftTree rightTree : Parenthesization n},
          IsInterval i.val leftLength leftTree →
          IsInterval (i.val + leftLength) rightLength rightTree →
          leftLength + rightLength = intervalLength i j →
          leftLength ≤ count →
          cell.cost ≤ scalarMultiplicationCost dimensions (.multiply leftTree rightTree) ∧
            (cell.cost = scalarMultiplicationCost dimensions (.multiply leftTree rightTree) →
              ∃ k, cell.split = some k ∧ k.val < i.val + leftLength)

theorem initialTable_correct {n : Nat} (dimensions : Vector Nat (n + 1)) :
    TableCorrectThrough dimensions (initialTable n) 1 := by
  intro i j hij hLength
  have hEq : i = j := by
    apply Fin.ext
    simp only [intervalLength] at hLength
    omega
  subst j
  let cell : Cell n := (0, none, .matrix i)
  refine ⟨cell, ?_, ?_, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · simp [tableGet, initialTable, cell, Vector.get_ofFn]
  · refine ⟨?_, rfl, ?_⟩
    · simpa [intervalLength, cell, Cell.witness] using IsInterval.matrix i
    · intro tree hTree
      exact Nat.zero_le _

theorem combine_interval {n : Nat} {i j k next : Fin n}
    (hik : i.val ≤ k.val) (hkj : k.val < j.val) (hNext : next.val = k.val + 1)
    {leftTree rightTree : Parenthesization n}
    (hLeft : IsInterval i.val (intervalLength i k) leftTree)
    (hRight : IsInterval next.val (intervalLength next j) rightTree) :
    IsInterval i.val (intervalLength i j) (.multiply leftTree rightTree) := by
  have hStart : i.val + intervalLength i k = next.val := by
    simp only [intervalLength]
    omega
  have hRight' : IsInterval (i.val + intervalLength i k)
      (intervalLength next j) rightTree := by
    simpa only [hStart] using hRight
  have combined := IsInterval.multiply hLeft hRight'
  have hLength : intervalLength i k + intervalLength next j = intervalLength i j := by
    simp only [intervalLength]
    omega
  simpa only [hLength] using combined

theorem candidate_cost_le {n : Nat} (dimensions : Vector Nat (n + 1))
    {i j k next : Fin n} {left right : Cell n}
    (hik : i.val ≤ k.val) (hkj : k.val < j.val) (hNext : next.val = k.val + 1)
    (hLeft : CellOptimal dimensions i k left)
    (hRight : CellOptimal dimensions next j right)
    {leftTree rightTree : Parenthesization n}
    (hLeftTree : IsInterval i.val (intervalLength i k) leftTree)
    (hRightTree : IsInterval next.val (intervalLength next j) rightTree) :
    left.cost + right.cost +
        dimensions.get i.castSucc * dimensions.get k.succ * dimensions.get j.succ ≤
      scalarMultiplicationCost dimensions (.multiply leftTree rightTree) := by
  have hLeftBound := hLeft.2.2 leftTree hLeftTree
  have hRightBound := hRight.2.2 rightTree hRightTree
  simp only [scalarMultiplicationCost]
  rw [hLeftTree.rows_eq dimensions, hLeftTree.cols_eq dimensions,
    hRightTree.cols_eq dimensions]
  have hLeftEnd : i.val + intervalLength i k = k.val + 1 := by
    simp only [intervalLength]
    omega
  have hRightEnd : next.val + intervalLength next j = j.val + 1 := by
    simp only [intervalLength]
    omega
  have hRows :
      dimensions.get ⟨i.val, by omega⟩ = dimensions.get i.castSucc := by
    congr 1
  have hMiddle :
      dimensions.get ⟨i.val + intervalLength i k, by omega⟩ = dimensions.get k.succ := by
    exact congrArg dimensions.get (Fin.ext hLeftEnd)
  have hCols :
      dimensions.get ⟨next.val + intervalLength next j, by omega⟩ = dimensions.get j.succ := by
    exact congrArg dimensions.get (Fin.ext hRightEnd)
  rw [hRows, hMiddle, hCols]
  omega

theorem candidate_cost_eq_witness {n : Nat}
    (dimensions : Vector Nat (n + 1)) {i j k next : Fin n}
    {left right : Cell n} (hik : i.val ≤ k.val) (hkj : k.val < j.val)
    (hNext : next.val = k.val + 1)
    (hLeft : CellOptimal dimensions i k left)
    (hRight : CellOptimal dimensions next j right) :
    scalarMultiplicationCost dimensions (.multiply left.witness right.witness) =
      left.cost + right.cost +
        dimensions.get i.castSucc * dimensions.get k.succ * dimensions.get j.succ := by
  simp only [scalarMultiplicationCost, hLeft.2.1, hRight.2.1]
  rw [hLeft.1.rows_eq dimensions, hLeft.1.cols_eq dimensions,
    hRight.1.cols_eq dimensions]
  have hLeftEnd : i.val + intervalLength i k = k.val + 1 := by
    simp only [intervalLength]
    omega
  have hRightEnd : next.val + intervalLength next j = j.val + 1 := by
    simp only [intervalLength]
    omega
  have hRows : dimensions.get ⟨i.val, by omega⟩ = dimensions.get i.castSucc := by
    congr 1
  have hMiddle :
      dimensions.get ⟨i.val + intervalLength i k, by omega⟩ = dimensions.get k.succ := by
    exact congrArg dimensions.get (Fin.ext hLeftEnd)
  have hCols :
      dimensions.get ⟨next.val + intervalLength next j, by omega⟩ = dimensions.get j.succ := by
    exact congrArg dimensions.get (Fin.ext hRightEnd)
  rw [hRows, hMiddle, hCols]

theorem combine_cost_eq {n : Nat} (dimensions : Vector Nat (n + 1))
    {i j k next : Fin n} (hik : i.val ≤ k.val) (hkj : k.val < j.val)
    (hNext : next.val = k.val + 1) {leftTree rightTree : Parenthesization n}
    (hLeftInterval : IsInterval i.val (intervalLength i k) leftTree)
    (hRightInterval : IsInterval next.val (intervalLength next j) rightTree)
    {leftCost rightCost : Nat}
    (hLeftCost : scalarMultiplicationCost dimensions leftTree = leftCost)
    (hRightCost : scalarMultiplicationCost dimensions rightTree = rightCost) :
    scalarMultiplicationCost dimensions (.multiply leftTree rightTree) =
      leftCost + rightCost +
        dimensions.get i.castSucc * dimensions.get k.succ * dimensions.get j.succ := by
  simp only [scalarMultiplicationCost, hLeftCost, hRightCost]
  rw [hLeftInterval.rows_eq dimensions, hLeftInterval.cols_eq dimensions,
    hRightInterval.cols_eq dimensions]
  have hLeftEnd : i.val + intervalLength i k = k.val + 1 := by
    simp only [intervalLength]
    omega
  have hRightEnd : next.val + intervalLength next j = j.val + 1 := by
    simp only [intervalLength]
    omega
  have hRows : dimensions.get ⟨i.val, by omega⟩ = dimensions.get i.castSucc := by
    congr 1
  have hMiddle :
      dimensions.get ⟨i.val + intervalLength i k, by omega⟩ = dimensions.get k.succ := by
    exact congrArg dimensions.get (Fin.ext hLeftEnd)
  have hCols :
      dimensions.get ⟨next.val + intervalLength next j, by omega⟩ = dimensions.get j.succ := by
    exact congrArg dimensions.get (Fin.ext hRightEnd)
  rw [hRows, hMiddle, hCols]

theorem scanSplits_correct {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (maxLength : Nat)
    (hTable : TableCorrectThrough dimensions table maxLength)
    (i j : Fin n) (hij : i.val < j.val)
    (hLength : intervalLength i j = maxLength + 1)
    (count : Nat) (hCount : i.val + count ≤ j.val) :
    PartialBestCorrect dimensions table i j count
      (scanSplits dimensions table i j count hCount).ret := by
  induction count with
  | zero => simp [scanSplits, matrixChainOrderRaw.scanSplits, PartialBestCorrect]
  | succ count ih =>
      let k : Fin n := ⟨i.val + count, by omega⟩
      let next : Fin n := ⟨i.val + count + 1, by omega⟩
      have hik : i.val ≤ k.val := by simp [k]
      have hkj : k.val < j.val := by simp [k]; omega
      have hNext : next.val = k.val + 1 := by simp [next, k]
      have hRightStart : i.val + intervalLength i k = next.val := by
        simp only [intervalLength, k, next]
        omega
      have hLeftLength : intervalLength i k ≤ maxLength := by
        simp only [intervalLength, k]
        simp only [intervalLength] at hLength
        omega
      have hRightLength : intervalLength next j ≤ maxLength := by
        simp only [intervalLength, next]
        simp only [intervalLength] at hLength
        omega
      obtain ⟨left, hLeftGet, hLeftOptimal, hLeftSplit, hLeftFirst⟩ :=
        hTable i k hik hLeftLength
      obtain ⟨right, hRightGet, hRightOptimal, hRightSplit, hRightFirst⟩ :=
        hTable next j (by
          change i.val + count + 1 ≤ j.val
          omega) hRightLength
      let candidate : Cell n :=
        (left.cost + right.cost +
          dimensions.get i.castSucc * dimensions.get k.succ * dimensions.get j.succ,
          some k, .multiply left.witness right.witness)
      have hCandidateInterval :
          IsInterval i.val (intervalLength i j) candidate.witness := by
        exact combine_interval hik hkj hNext hLeftOptimal.1 hRightOptimal.1
      have hCandidateCost :
          scalarMultiplicationCost dimensions candidate.witness = candidate.cost := by
        exact candidate_cost_eq_witness dimensions hik hkj hNext hLeftOptimal hRightOptimal
      have hCandidateSplit : CellSplitCorrect dimensions table i j candidate := by
        right
        exact ⟨k, next, left, right, hik, hkj, rfl, hNext, hLeftGet, hRightGet, rfl, rfl⟩
      have hPrevious := ih (by omega)
      simp only [scanSplits, matrixChainOrderRaw.scanSplits, TimeM.ret_bind]
      change PartialBestCorrect dimensions table i j (count + 1) _
      rw [show (⟨i.val + count, by omega⟩ : Fin n) = k by rfl]
      rw [show (⟨i.val + count + 1, by omega⟩ : Fin n) = next by rfl]
      rw [hLeftGet, hRightGet]
      simp only [TimeM.ret_pure]
      cases hPrev : (scanSplits dimensions table i j count (by omega)).ret with
      | none =>
          simp only
          change PartialBestCorrect dimensions table i j (count + 1) (some candidate)
          have hCountZero : count = 0 := by
            simpa [hPrev, PartialBestCorrect] using hPrevious
          subst count
          refine ⟨hCandidateInterval, hCandidateCost, hCandidateSplit,
            ⟨k, rfl, by simp [k]⟩, ?_⟩
          intro leftLength rightLength leftTree rightTree hLeftTree hRightTree hTotal hBound
          have hLeftPos := hLeftTree.length_pos
          have hLeftLengthEq : leftLength = intervalLength i k := by
            simp only [k, intervalLength]
            omega
          have hRightLengthEq : rightLength = intervalLength next j := by
            simp only [next, intervalLength] at hTotal ⊢
            simp only [intervalLength] at hLength
            omega
          constructor
          · apply candidate_cost_le dimensions hik hkj hNext hLeftOptimal hRightOptimal
            · simpa only [hLeftLengthEq] using hLeftTree
            · have hRightTree' : IsInterval next.val rightLength rightTree := by
                simpa only [hLeftLengthEq, hRightStart] using hRightTree
              simpa only [hRightLengthEq] using hRightTree'
          · intro hEqual
            exact ⟨k, rfl, by simp only [k]; omega⟩
      | some current =>
          simp only
          change PartialBestCorrect dimensions table i j (count + 1)
            (if candidate.cost < current.cost then some candidate else some current)
          have hCurrent : PartialBestCorrect dimensions table i j count (some current) := by
            simpa only [hPrev] using hPrevious
          by_cases hImprove : candidate.cost < current.cost
          · simp only [hImprove, ↓reduceIte]
            refine ⟨hCandidateInterval, hCandidateCost, hCandidateSplit,
              ⟨k, rfl, by simp [k]⟩, ?_⟩
            intro leftLength rightLength leftTree rightTree hLeftTree hRightTree hTotal hBound
            constructor
            · by_cases hOld : leftLength ≤ count
              · exact (Nat.le_of_lt hImprove).trans
                  (hCurrent.2.2.2.2 hLeftTree hRightTree hTotal hOld).1
              · have hLeftLengthEq : leftLength = intervalLength i k := by
                  simp only [k, intervalLength]
                  omega
                have hRightLengthEq : rightLength = intervalLength next j := by
                  simp only [next, intervalLength] at hTotal ⊢
                  simp only [intervalLength] at hLength
                  omega
                apply candidate_cost_le dimensions hik hkj hNext hLeftOptimal hRightOptimal
                · simpa only [hLeftLengthEq] using hLeftTree
                · have hRightTree' : IsInterval next.val rightLength rightTree := by
                    simpa only [hLeftLengthEq, hRightStart] using hRightTree
                  simpa only [hRightLengthEq] using hRightTree'
            · intro hEqual
              refine ⟨k, rfl, ?_⟩
              by_cases hOld : leftLength ≤ count
              · have hOldBound :=
                  (hCurrent.2.2.2.2 hLeftTree hRightTree hTotal hOld).1
                omega
              · simp only [k]
                omega
          · simp only [hImprove, ↓reduceIte]
            obtain ⟨selected, hSelectedSplit, hSelectedBound⟩ := hCurrent.2.2.2.1
            refine ⟨hCurrent.1, hCurrent.2.1, hCurrent.2.2.1,
              ⟨selected, hSelectedSplit, by omega⟩, ?_⟩
            intro leftLength rightLength leftTree rightTree hLeftTree hRightTree hTotal hBound
            constructor
            · by_cases hOld : leftLength ≤ count
              · exact (hCurrent.2.2.2.2 hLeftTree hRightTree hTotal hOld).1
              · have hLeftLengthEq : leftLength = intervalLength i k := by
                  simp only [k, intervalLength]
                  omega
                have hRightLengthEq : rightLength = intervalLength next j := by
                  simp only [next, intervalLength] at hTotal ⊢
                  simp only [intervalLength] at hLength
                  omega
                have hCandidateBound :=
                  candidate_cost_le dimensions hik hkj hNext hLeftOptimal hRightOptimal
                    (by simpa only [hLeftLengthEq] using hLeftTree)
                    (by
                      have hRightTree' : IsInterval next.val rightLength rightTree := by
                        simpa only [hLeftLengthEq, hRightStart] using hRightTree
                      simpa only [hRightLengthEq] using hRightTree')
                exact (Nat.le_of_not_gt hImprove).trans hCandidateBound
            · intro hEqual
              by_cases hOld : leftLength ≤ count
              · exact (hCurrent.2.2.2.2 hLeftTree hRightTree hTotal hOld).2 hEqual
              · exact ⟨selected, hSelectedSplit, by omega⟩

theorem CellSplitCorrect.tableSet_of_not_shorter {n : Nat}
    (dimensions : Vector Nat (n + 1)) (table : Table n)
    {p q : Fin n} {cell : Cell n} (hSplit : CellSplitCorrect dimensions table p q cell)
    (i j : Fin n) (value : Option (Cell n))
    (hNotShorter : intervalLength p q ≤ intervalLength i j) :
    CellSplitCorrect dimensions (tableSet table i j value) p q cell := by
  rcases hSplit with hDiagonal | ⟨k, next, left, right, hpk, hkq, hCellSplit,
      hNext, hLeftGet, hRightGet, hCost, hWitness⟩
  · exact Or.inl hDiagonal
  · right
    have hLeftNe : p ≠ i ∨ k ≠ j := by
      by_contra h
      push Not at h
      rcases h with ⟨rfl, rfl⟩
      simp only [intervalLength] at hNotShorter
      omega
    have hRightNe : next ≠ i ∨ q ≠ j := by
      by_contra h
      push Not at h
      rcases h with ⟨rfl, rfl⟩
      simp only [intervalLength] at hNotShorter
      omega
    refine ⟨k, next, left, right, hpk, hkq, hCellSplit, hNext, ?_, ?_, hCost,
      hWitness⟩
    · rw [tableGet_tableSet_of_ne table i j p k value hLeftNe]
      exact hLeftGet
    · rw [tableGet_tableSet_of_ne table i j next q value hRightNe]
      exact hRightGet

theorem TableCorrectThrough.tableSet_of_longer {n : Nat}
    (dimensions : Vector Nat (n + 1)) (table : Table n) (maxLength : Nat)
    (hTable : TableCorrectThrough dimensions table maxLength)
    (i j : Fin n) (value : Option (Cell n))
    (hLonger : maxLength < intervalLength i j) :
    TableCorrectThrough dimensions (tableSet table i j value) maxLength := by
  intro p q hpq hLength
  obtain ⟨cell, hGet, hOptimal, hSplit, hFirst⟩ := hTable p q hpq hLength
  have hNe : p ≠ i ∨ q ≠ j := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    omega
  refine ⟨cell, ?_, hOptimal, ?_, hFirst⟩
  · rw [tableGet_tableSet_of_ne table i j p q value hNe]
    exact hGet
  · exact hSplit.tableSet_of_not_shorter dimensions table i j value (by omega)

def StartsCorrect {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (length count : Nat) : Prop :=
  TableCorrectThrough dimensions table (length - 1) ∧
    ∀ (i j : Fin n), i.val < j.val → intervalLength i j = length → i.val < count →
      ∃ cell, tableGet table i j = some cell ∧
        CellOptimal dimensions i j cell ∧ CellSplitCorrect dimensions table i j cell ∧
          CellFirstAttainingSplit dimensions i j cell

theorem fillStarts_correct {n : Nat} (dimensions : Vector Nat (n + 1))
    (length : Nat) (hLength : 2 ≤ length) (hLengthN : length ≤ n)
    (count : Nat) (hCount : count ≤ n - length + 1) (table : Table n)
    (hTable : TableCorrectThrough dimensions table (length - 1)) :
    StartsCorrect dimensions
      (fillStarts dimensions length hLength hLengthN count hCount table).ret length count := by
  induction count generalizing table with
  | zero =>
      refine ⟨by simpa [fillStarts, matrixChainOrderRaw.fillStarts] using hTable, ?_⟩
      intro i j hij hInterval hStart
      omega
  | succ count ih =>
      let previous :=
        (fillStarts dimensions length hLength hLengthN count (by omega) table).ret
      have hPrevious : StartsCorrect dimensions previous length count :=
        ih (by omega) table hTable
      let i : Fin n := ⟨count, by omega⟩
      let j : Fin n := ⟨count + length - 1, by omega⟩
      have hij : i.val < j.val := by simp [i, j]; omega
      have hInterval : intervalLength i j = length := by
        simp only [intervalLength, i, j]
        omega
      have hScanBound : i.val + (length - 1) ≤ j.val := by
        simp only [i, j]
        omega
      have hScan := scanSplits_correct dimensions previous (length - 1)
        hPrevious.1 i j hij (by omega) (length - 1) hScanBound
      let best := (scanSplits dimensions previous i j (length - 1) hScanBound).ret
      have hBest : PartialBestCorrect dimensions previous i j (length - 1) best := hScan
      obtain ⟨cell, hBestEq⟩ : ∃ cell, best = some cell := by
        cases hValue : best with
        | none =>
            have : length - 1 = 0 := by
              simpa [best, hValue, PartialBestCorrect] using hBest
            omega
        | some cell => exact ⟨cell, rfl⟩
      have hCell : PartialBestCorrect dimensions previous i j (length - 1) (some cell) := by
        simpa only [hBestEq] using hBest
      have hOptimal : CellOptimal dimensions i j cell := by
        refine ⟨hCell.1, hCell.2.1, ?_⟩
        intro tree hTree
        obtain ⟨leftLength, rightLength, leftTree, rightTree, rfl, hLeft, hRight,
          hTotal⟩ := hTree.split_of_one_lt (by omega)
        have hRightPos := hRight.length_pos
        have hBound : leftLength ≤ length - 1 := by omega
        exact (hCell.2.2.2.2 hLeft hRight hTotal hBound).1
      have hSplitUpdated :
          CellSplitCorrect dimensions (tableSet previous i j (some cell)) i j cell :=
        hCell.2.2.1.tableSet_of_not_shorter dimensions previous i j (some cell) (by omega)
      have hFirst : CellFirstAttainingSplit dimensions i j cell := by
        right
        intro leftLength rightLength leftTree rightTree hLeft hRight hTotal hEqual
        have hLeftPos := hLeft.length_pos
        have hRightPos := hRight.length_pos
        have hBound : leftLength ≤ length - 1 := by
          simp only [hInterval] at hTotal
          omega
        exact (hCell.2.2.2.2 hLeft hRight hTotal hBound).2 hEqual
      have hFillRet :
          (fillStarts dimensions length hLength hLengthN (count + 1) hCount table).ret =
            tableSet previous i j (some cell) := by
        simp only [fillStarts, matrixChainOrderRaw.fillStarts, TimeM.ret_bind]
        rw [show
          (scanSplits dimensions previous i j (length - 1) hScanBound).ret = some cell by
            exact hBestEq]
        rfl
      rw [hFillRet]
      constructor
      · exact TableCorrectThrough.tableSet_of_longer dimensions previous (length - 1)
          hPrevious.1 i j (some cell) (by omega)
      · intro p q hpq hLengthPQ hStart
        by_cases hp : p = i
        · subst p
          have hq : q = j := by
            apply Fin.ext
            simp only [intervalLength] at hLengthPQ hInterval
            omega
          subst q
          refine ⟨cell, tableGet_tableSet_self previous i j (some cell), hOptimal,
            ?_, hFirst⟩
          exact hSplitUpdated
        · obtain ⟨oldCell, hOldGet, hOldOptimal, hOldSplit, hOldFirst⟩ :=
            hPrevious.2 p q hpq hLengthPQ (by
              have hpVal : p.val ≠ count := by
                intro hEq
                apply hp
                apply Fin.ext
                simpa [i] using hEq
              omega)
          have hNe : p ≠ i ∨ q ≠ j := Or.inl hp
          refine ⟨oldCell, ?_, hOldOptimal, ?_, hOldFirst⟩
          · rw [tableGet_tableSet_of_ne previous i j p q (some cell) hNe]
            exact hOldGet
          · exact CellSplitCorrect.tableSet_of_not_shorter dimensions previous hOldSplit
              i j (some cell) (by omega)

theorem fillStarts_complete {n : Nat} (dimensions : Vector Nat (n + 1))
    (length : Nat) (hLength : 2 ≤ length) (hLengthN : length ≤ n)
    (table : Table n) (hTable : TableCorrectThrough dimensions table (length - 1)) :
    TableCorrectThrough dimensions
      (fillStarts dimensions length hLength hLengthN (n - length + 1) (by omega) table).ret
      length := by
  have hStarts := fillStarts_correct dimensions length hLength hLengthN
    (n - length + 1) (by omega) table hTable
  intro i j hij hInterval
  by_cases hShort : intervalLength i j ≤ length - 1
  · exact hStarts.1 i j hij hShort
  · have hExact : intervalLength i j = length := by omega
    have hlt : i.val < j.val := by
      simp only [intervalLength] at hExact
      omega
    have hStart : i.val < n - length + 1 := by
      have hj := j.isLt
      simp only [intervalLength] at hExact
      omega
    exact hStarts.2 i j hlt hExact hStart

theorem fillLengths_correct {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) (count : Nat) (hCount : count ≤ n - 1) :
    TableCorrectThrough dimensions (fillLengths dimensions hn count hCount).ret (count + 1) := by
  induction count with
  | zero =>
      simpa [fillLengths, matrixChainOrderRaw.fillLengths] using initialTable_correct dimensions
  | succ count ih =>
      simp only [fillLengths, matrixChainOrderRaw.fillLengths, TimeM.ret_bind]
      let previous := (fillLengths dimensions hn count (by omega)).ret
      have hPrevious : TableCorrectThrough dimensions previous (count + 1) := ih (by omega)
      let length := count + 2
      have hComplete := fillStarts_complete dimensions length (by omega) (by omega)
        previous (by simpa [length] using hPrevious)
      simpa [length] using hComplete

theorem buildTable_correct {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) : TableCorrectThrough dimensions (buildTable dimensions hn).ret n := by
  have hLength : n - 1 + 1 = n := by omega
  have hCorrect := fillLengths_correct dimensions hn (n - 1) (by omega)
  simpa only [buildTable, hLength] using hCorrect

end Internal

end Cslib.Algorithms.Lean.MatrixChain
