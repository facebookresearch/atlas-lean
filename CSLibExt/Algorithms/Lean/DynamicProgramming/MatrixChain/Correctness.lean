/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain.Basic
public import Mathlib.Data.Nat.Choose.Basic

import all CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain.Internal.Reconstruction

/-!
# Matrix-chain correctness and cost bounds

Public correctness, exact event-count, and cubic-bound theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MatrixChain

open Cslib.Algorithms.Lean
open Internal

private theorem matrixChainOrderRaw_spec {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) :
    ∃ (cell : Cell n) (tree : Parenthesization n),
      (matrixChainOrderRaw dimensions hn).ret =
          some { optimalCost := cell.cost, parenthesization := tree } ∧
        CellOptimal dimensions ⟨0, hn⟩ ⟨n - 1, by omega⟩ cell ∧
        IsInterval 0 n tree ∧ scalarMultiplicationCost dimensions tree = cell.cost := by
  let table := (buildTable dimensions hn).ret
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hTable := buildTable_correct dimensions hn
  have hInterval : intervalLength first last = n := by
    simp only [intervalLength, first, last]
    omega
  have hFirstLast : first.val ≤ last.val := by
    simp only [first, last]
    omega
  obtain ⟨cell, hCell, hOptimal, hSplit, hFirst⟩ :=
    hTable first last (by simp [first, last]) (by simp [hInterval])
  obtain ⟨tree, hTree, hTreeInterval, hTreeCost⟩ :=
    reconstruct_correct dimensions table n hTable n first last
      hFirstLast (by simp [hInterval]) (by simp [hInterval]) cell hCell
  refine ⟨cell, tree, ?_, ?_, ?_, hTreeCost⟩
  · unfold matrixChainOrderRaw
    simp only [TimeM.ret_bind]
    dsimp only [tableGet, tableSet, buildTable, fillLengths, initialTable, first, last] at hCell
    rw [hCell]
    simp only [TimeM.ret_bind]
    dsimp only [reconstruct?, tableGet, tableSet, table, buildTable, fillLengths,
      initialTable, first, last] at hTree
    rw [hTree]
    rfl
  · simpa only [first, last] using hOptimal
  · simpa only [hInterval, first] using hTreeInterval

/-- Compute an optimal matrix-chain scalar cost and reconstruct one attaining tree. -/
public def matrixChainOrder {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) : TimeM Cost (Result n) :=
  let computation := matrixChainOrderRaw dimensions hn
  have hSome : computation.ret.isSome := by
    obtain ⟨cell, tree, hResult, hOptimal, hInterval, hCost⟩ :=
      matrixChainOrderRaw_spec dimensions hn
    change (matrixChainOrderRaw dimensions hn).ret.isSome
    rw [hResult]
    rfl
  { ret := computation.ret.get hSome, time := computation.time }

private theorem matrixChainOrder_spec {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) :
    ∃ (cell : Cell n) (tree : Parenthesization n),
      (matrixChainOrder dimensions hn).ret =
          { optimalCost := cell.cost, parenthesization := tree } ∧
        CellOptimal dimensions ⟨0, hn⟩ ⟨n - 1, by omega⟩ cell ∧
        IsInterval 0 n tree ∧ scalarMultiplicationCost dimensions tree = cell.cost := by
  obtain ⟨cell, tree, hResult, hOptimal, hInterval, hCost⟩ :=
    matrixChainOrderRaw_spec dimensions hn
  refine ⟨cell, tree, ?_, hOptimal, hInterval, hCost⟩
  unfold matrixChainOrder
  dsimp only
  apply Option.some_injective _
  exact (Option.some_get _).trans hResult

/-- The returned parenthesization uses every matrix once in order and is dimension-valid. -/
public theorem matrixChainOrder_parenthesization_valid {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    let result := (matrixChainOrder dimensions hn).ret
    result.parenthesization.IsValid dimensions := by
  obtain ⟨cell, tree, hResult, hOptimal, hInterval, hCost⟩ :=
    matrixChainOrder_spec dimensions hn
  simp only [hResult]
  constructor
  · apply (List.map_injective_iff.mpr Fin.val_injective)
    calc
      tree.matrixIndices.map (fun index => index.val) = List.range' 0 n :=
        hInterval.indices
      _ = List.range n := List.range_eq_range'.symm
      _ = (List.finRange n).map (fun index => index.val) :=
        List.map_coe_finRange_eq_range.symm
  · exact hInterval.compatible dimensions

/-- The reported optimum is the scalar cost of the returned parenthesization. -/
public theorem matrixChainOrder_cost_eq {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) :
    let result := (matrixChainOrder dimensions hn).ret
    scalarMultiplicationCost dimensions result.parenthesization = result.optimalCost := by
  obtain ⟨cell, tree, hResult, hOptimal, hInterval, hCost⟩ :=
    matrixChainOrder_spec dimensions hn
  simpa only [hResult] using hCost

/-- Every valid parenthesization costs at least the reported optimum. -/
public theorem matrixChainOrder_minimal {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) (tree : Parenthesization n) (hTree : tree.IsValid dimensions) :
    (matrixChainOrder dimensions hn).ret.optimalCost ≤
      scalarMultiplicationCost dimensions tree := by
  obtain ⟨cell, resultTree, hResult, hOptimal, hInterval, hCost⟩ :=
    matrixChainOrder_spec dimensions hn
  rw [hResult]
  apply hOptimal.2.2
  have hCandidate : IsInterval 0 n tree := by
    apply isInterval_of_indices (start := 0) (length := n) tree
    calc
      tree.matrixIndices.map (fun index => index.val) =
          (List.finRange n).map (fun index => index.val) := congrArg _ hTree.1
      _ = List.range n := List.map_coe_finRange_eq_range
      _ = List.range' 0 n := List.range_eq_range'
  have hFinalLength : intervalLength (⟨0, hn⟩ : Fin n) ⟨n - 1, by omega⟩ = n := by
    simp only [intervalLength]
    omega
  simpa only [hFinalLength] using hCandidate

private theorem matrixChainOrder_time_fields {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    (matrixChainOrder dimensions hn).time.candidateEvaluations =
        Nat.choose (n + 1) 3 ∧
      (matrixChainOrder dimensions hn).time.reconstructionNodes = 2 * n - 1 := by
  let table := (buildTable dimensions hn).ret
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hTable := buildTable_correct dimensions hn
  have hInterval : intervalLength first last = n := by
    simp only [intervalLength, first, last]
    omega
  have hFirstLast : first.val ≤ last.val := by
    simp only [first, last]
    omega
  obtain ⟨cell, hCell, hOptimal, hSplit, hFirst⟩ :=
    hTable first last (by simp [first, last]) (by simp [hInterval])
  have hReconstruct := reconstruct_time dimensions table n hTable n first last hFirstLast
    (by simp [hInterval]) (by simp [hInterval]) cell hCell
  have hBuildCandidates :
      (buildTable dimensions hn).time.candidateEvaluations = Nat.choose (n + 1) 3 := by
    rw [buildTable, fillLengths_candidateEvaluations, candidateCountFor_full,
      candidateCount_eq_choose]
  have hBuildReconstruction :
      (buildTable dimensions hn).time.reconstructionNodes = 0 := by
    rw [buildTable, fillLengths_reconstructionNodes]
  unfold matrixChainOrder matrixChainOrderRaw
  simp only [TimeM.time_bind]
  dsimp only [tableGet, tableSet, buildTable, fillLengths, initialTable, first, last] at hCell
  rw [hCell]
  simp only [TimeM.time_bind]
  dsimp only [reconstruct?, tableGet, tableSet, table, buildTable, fillLengths,
    initialTable, first, last] at hReconstruct
  dsimp only [buildTable, fillLengths] at hBuildCandidates hBuildReconstruction
  constructor
  · simp only [add_candidateEvaluations, hBuildCandidates, hReconstruct.1, zero_add]
    split <;> rfl
  · simp only [add_reconstructionNodes, hBuildReconstruction, hReconstruct.2, zero_add]
    split <;> simp [hInterval, first, last]

/-- The dynamic program evaluates exactly one candidate for every interval split. -/
public theorem matrixChainOrder_candidateEvaluations {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    (matrixChainOrder dimensions hn).time.candidateEvaluations = Nat.choose (n + 1) 3 :=
  (matrixChainOrder_time_fields dimensions hn).1

/-- Reconstruction emits and charges exactly the nodes of a full binary tree. -/
public theorem matrixChainOrder_reconstructionNodes {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    (matrixChainOrder dimensions hn).time.reconstructionNodes = 2 * n - 1 :=
  (matrixChainOrder_time_fields dimensions hn).2

/-- The total event count is the split count plus the reconstructed-tree size. -/
public theorem matrixChainOrder_time {n : Nat} (dimensions : Vector Nat (n + 1))
    (hn : 0 < n) :
    (matrixChainOrder dimensions hn).time.total =
      Nat.choose (n + 1) 3 + (2 * n - 1) := by
  simp only [Cost.total, matrixChainOrder_candidateEvaluations,
    matrixChainOrder_reconstructionNodes]

/-- The declared event count is bounded above by three times the cube of chain length. -/
public theorem matrixChainOrder_time_le_three_mul_cube {n : Nat}
    (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    (matrixChainOrder dimensions hn).time.total ≤ 3 * n ^ 3 := by
  rw [matrixChainOrder_time]
  rw [← candidateCount_eq_choose]
  have hCandidate := candidateCount_le_cube n
  have hnOne : 1 ≤ n := hn
  have hCube : n ≤ n ^ 3 := by
    calc
      n = n * 1 := by omega
      _ ≤ n * (n * n) := by
        apply Nat.mul_le_mul_left
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]
  calc
    candidateCount n + (2 * n - 1) ≤ n ^ 3 + 2 * n := by omega
    _ ≤ n ^ 3 + 2 * n ^ 3 := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hCube) _
    _ = 3 * n ^ 3 := by omega

end Cslib.Algorithms.Lean.MatrixChain
