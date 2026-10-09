/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain.Internal.Optimality

/-!
# Matrix-chain reconstruction internals

Stored splits reconstruct a valid optimum and charge one event per tree node.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MatrixChain

open Cslib.Algorithms.Lean

namespace Internal

abbrev reconstruct? {n : Nat} (table : Table n) :
    (fuel : Nat) → (i j : Fin n) → i.val ≤ j.val →
      TimeM Cost (Option (Parenthesization n)) :=
  matrixChainOrderRaw.reconstruct? tableGet table

theorem reconstruct_correct {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (maxLength : Nat)
    (hTable : TableCorrectThrough dimensions table maxLength)
    (fuel : Nat) (i j : Fin n) (hij : i.val ≤ j.val)
    (hFuel : intervalLength i j ≤ fuel) (hLength : intervalLength i j ≤ maxLength)
    (cell : Cell n) (hGet : tableGet table i j = some cell) :
    ∃ tree, (reconstruct? table fuel i j hij).ret = some tree ∧
      IsInterval i.val (intervalLength i j) tree ∧
      scalarMultiplicationCost dimensions tree = cell.cost := by
  induction fuel generalizing i j cell with
  | zero =>
      simp only [intervalLength] at hFuel
      omega
  | succ fuel ih =>
      obtain ⟨known, hKnownGet, hOptimal, hSplit, hFirst⟩ := hTable i j hij hLength
      have hKnown : known = cell := by
        exact Option.some.inj (hKnownGet.symm.trans hGet)
      subst known
      by_cases hEq : i = j
      · subst j
        have hIntervalOne : intervalLength i i = 1 := by simp [intervalLength]
        have hLeafInterval : IsInterval i.val (intervalLength i i) (.matrix i) := by
          simpa only [hIntervalOne] using IsInterval.matrix i
        have hCostLe := hOptimal.2.2 (.matrix i) hLeafInterval
        have hCostZero : cell.cost = 0 := Nat.eq_zero_of_le_zero hCostLe
        refine ⟨.matrix i, ?_, hLeafInterval, ?_⟩
        · simp [reconstruct?, matrixChainOrderRaw.reconstruct?]
        · simp [scalarMultiplicationCost, hCostZero]
      · have hijStrict : i.val < j.val := by
          have hijNe : i.val ≠ j.val := fun h => hEq (Fin.ext h)
          omega
        rcases hSplit with hDiagonal |
          ⟨k, next, left, right, hik, hkj, hCellSplit, hNext, hLeftGet,
            hRightGet, hCellCost, hCellWitness⟩
        · exact (hEq hDiagonal.1).elim
        · have hNextEq : next = ⟨k.val + 1, by omega⟩ := by
            apply Fin.ext
            exact hNext
          have hLeftLength : intervalLength i k < intervalLength i j := by
            simp only [intervalLength]
            omega
          have hRightLength : intervalLength next j < intervalLength i j := by
            simp only [intervalLength]
            omega
          have hLeftFuel : intervalLength i k ≤ fuel := by omega
          have hRightFuel : intervalLength next j ≤ fuel := by omega
          have hLeftMax : intervalLength i k ≤ maxLength := by omega
          have hRightMax : intervalLength next j ≤ maxLength := by omega
          obtain ⟨leftTree, hLeftRet, hLeftInterval, hLeftCost⟩ :=
            ih i k hik hLeftFuel hLeftMax left hLeftGet
          obtain ⟨rightTree, hRightRet, hRightInterval, hRightCost⟩ :=
            ih next j (by omega) hRightFuel hRightMax right hRightGet
          have hRightRetAlgorithm :
              (reconstruct? table fuel (⟨k.val + 1, by omega⟩ : Fin n) j (by omega)).ret =
                some rightTree := by
            simpa only [← hNextEq] using hRightRet
          have hCellSplitRaw : cell.2.1 = some k := by
            simpa only [Cell.split] using hCellSplit
          have hSplitRaw : i ≤ k ∧ k < j := ⟨hik, hkj⟩
          refine ⟨.multiply leftTree rightTree, ?_, ?_, ?_⟩
          · simp [reconstruct?, matrixChainOrderRaw.reconstruct?, hEq, hGet, hCellSplitRaw,
              hSplitRaw, hLeftRet, hRightRetAlgorithm]
          · exact combine_interval hik hkj hNext hLeftInterval hRightInterval
          · rw [hCellCost]
            exact combine_cost_eq dimensions hik hkj hNext hLeftInterval hRightInterval
              hLeftCost hRightCost

theorem reconstruct_time {n : Nat} (dimensions : Vector Nat (n + 1))
    (table : Table n) (maxLength : Nat)
    (hTable : TableCorrectThrough dimensions table maxLength)
    (fuel : Nat) (i j : Fin n) (hij : i.val ≤ j.val)
    (hFuel : intervalLength i j ≤ fuel) (hLength : intervalLength i j ≤ maxLength)
    (cell : Cell n) (hGet : tableGet table i j = some cell) :
    (reconstruct? table fuel i j hij).time.candidateEvaluations = 0 ∧
      (reconstruct? table fuel i j hij).time.reconstructionNodes =
        2 * intervalLength i j - 1 := by
  induction fuel generalizing i j cell with
  | zero =>
      simp only [intervalLength] at hFuel
      omega
  | succ fuel ih =>
      obtain ⟨known, hKnownGet, hOptimal, hSplit, hFirst⟩ := hTable i j hij hLength
      have hKnown : known = cell := Option.some.inj (hKnownGet.symm.trans hGet)
      subst known
      by_cases hEq : i = j
      · subst j
        constructor <;>
          simp [reconstruct?, matrixChainOrderRaw.reconstruct?, intervalLength]
      · rcases hSplit with hDiagonal |
          ⟨k, next, left, right, hik, hkj, hCellSplit, hNext, hLeftGet,
            hRightGet, hCellCost, hCellWitness⟩
        · exact (hEq hDiagonal.1).elim
        · have hNextEq : next = ⟨k.val + 1, by omega⟩ := Fin.ext hNext
          have hLeftLength : intervalLength i k < intervalLength i j := by
            simp only [intervalLength]
            omega
          have hRightLength : intervalLength next j < intervalLength i j := by
            simp only [intervalLength]
            omega
          have hLeftFuel : intervalLength i k ≤ fuel := by omega
          have hRightFuel : intervalLength next j ≤ fuel := by omega
          have hLeftMax : intervalLength i k ≤ maxLength := by omega
          have hRightMax : intervalLength next j ≤ maxLength := by omega
          have hLeftTime := ih i k hik hLeftFuel hLeftMax left hLeftGet
          have hRightTime := ih next j (by omega) hRightFuel hRightMax right hRightGet
          have hRightCandidateAlgorithm :
              (reconstruct? table fuel (⟨k.val + 1, by omega⟩ : Fin n) j
                (by omega)).time.candidateEvaluations = 0 := by
            simpa only [← hNextEq] using hRightTime.1
          have hRightNodesAlgorithm :
              (reconstruct? table fuel (⟨k.val + 1, by omega⟩ : Fin n) j
                (by omega)).time.reconstructionNodes = 2 * intervalLength next j - 1 := by
            simpa only [← hNextEq] using hRightTime.2
          have hCellSplitRaw : cell.2.1 = some k := by
            simpa only [Cell.split] using hCellSplit
          have hSplitRaw : i ≤ k ∧ k < j := ⟨hik, hkj⟩
          have hLengthSum : intervalLength i k + intervalLength next j =
              intervalLength i j := by
            simp only [intervalLength]
            omega
          constructor
          · simp [reconstruct?, matrixChainOrderRaw.reconstruct?, hEq, hGet, hCellSplitRaw,
              hSplitRaw, hLeftTime.1, hRightCandidateAlgorithm]
          · simp [reconstruct?, matrixChainOrderRaw.reconstruct?, hEq, hGet, hCellSplitRaw,
              hSplitRaw, hLeftTime.2, hRightNodesAlgorithm]
            have hLeftPos := (show 0 < intervalLength i k by
              simp only [intervalLength]
              omega)
            have hRightPos := (show 0 < intervalLength next j by
              simp only [intervalLength]
              omega)
            omega

end Internal

end Cslib.Algorithms.Lean.MatrixChain
