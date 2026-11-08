/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.MatrixChain

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MatrixChainTests

open MatrixChain

#check Parenthesization
#check Parenthesization.matrixIndices
#check Parenthesization.rows
#check Parenthesization.cols
#check Parenthesization.DimensionCompatible
#check Parenthesization.IsValid
#check scalarMultiplicationCost
#check Cost
#check Cost.total
#check Result
#check matrixChainOrder
#check matrixChainOrder_parenthesization_valid
#check matrixChainOrder_cost_eq
#check matrixChainOrder_minimal
#check matrixChainOrder_candidateEvaluations
#check matrixChainOrder_reconstructionNodes
#check matrixChainOrder_time
#check matrixChainOrder_time_le_three_mul_cube

example : IsEmpty (Parenthesization 0) := ⟨by
  intro tree
  induction tree with
  | matrix index => exact Fin.elim0 index
  | multiply _ _ leftImpossible _ => exact leftImpossible⟩

example : ¬ 0 < 0 := by decide

private def emptyDimensions : Vector Nat 1 := #v[10]

#guard emptyDimensions.toList == [10]

private def singletonDimensions : Vector Nat 2 := #v[10, 20]

#guard (matrixChainOrder singletonDimensions (by decide)).ret ==
  ({ optimalCost := 0, parenthesization := .matrix 0 } : Result 1)

#guard (matrixChainOrder singletonDimensions (by decide)).time ==
  { candidateEvaluations := 0, reconstructionNodes := 1 }

#guard (matrixChainOrder singletonDimensions (by decide)).time.total == 1

private def twoDimensions : Vector Nat 3 := #v[10, 20, 30]

#guard (matrixChainOrder twoDimensions (by decide)).ret ==
  ({ optimalCost := 6000, parenthesization := .multiply (.matrix 0) (.matrix 1) } : Result 2)

#guard (matrixChainOrder twoDimensions (by decide)).time ==
  { candidateEvaluations := 1, reconstructionNodes := 3 }

#guard (matrixChainOrder twoDimensions (by decide)).time.total == 4

private def cheaperLeftDimensions : Vector Nat 4 := #v[10, 100, 5, 50]

#guard (matrixChainOrder cheaperLeftDimensions (by decide)).ret ==
  ({ optimalCost := 7500,
     parenthesization := .multiply (.multiply (.matrix 0) (.matrix 1)) (.matrix 2) } : Result 3)

private def tieDimensions : Vector Nat 4 := #v[1, 1, 1, 1]

#guard (matrixChainOrder tieDimensions (by decide)).ret ==
  ({ optimalCost := 2,
     parenthesization := .multiply (.matrix 0) (.multiply (.matrix 1) (.matrix 2)) } : Result 3)

private def zeroDimension : Vector Nat 4 := #v[10, 0, 20, 30]

#guard (matrixChainOrder zeroDimension (by decide)).ret.optimalCost == 0

private def duplicateTree : Parenthesization 3 :=
  .multiply (.matrix 0) (.multiply (.matrix 0) (.matrix 2))

private def omittedTree : Parenthesization 3 :=
  .multiply (.matrix 0) (.matrix 2)

private def permutedTree : Parenthesization 3 :=
  .multiply (.matrix 1) (.multiply (.matrix 0) (.matrix 2))

example : ¬ duplicateTree.IsValid tieDimensions := by
  intro h
  have hIndices := h.1
  change [0, 0, 2] = List.finRange 3 at hIndices
  exact (show [0, 0, 2] ≠ List.finRange 3 by decide) hIndices

example : ¬ omittedTree.IsValid tieDimensions := by
  intro h
  have hIndices := h.1
  change [0, 2] = List.finRange 3 at hIndices
  exact (show [0, 2] ≠ List.finRange 3 by decide) hIndices

example : ¬ permutedTree.IsValid tieDimensions := by
  intro h
  have hIndices := h.1
  change [1, 0, 2] = List.finRange 3 at hIndices
  exact (show [1, 0, 2] ≠ List.finRange 3 by decide) hIndices

example : permutedTree.DimensionCompatible tieDimensions := by
  simp [permutedTree, tieDimensions, Parenthesization.DimensionCompatible,
    Parenthesization.rows, Parenthesization.cols]
  change 1 = 1 ∧ 1 = 1
  decide

private def incompatibleDimensions : Vector Nat 3 := #v[2, 3, 4]
private def incompatibleTree : Parenthesization 2 := .multiply (.matrix 1) (.matrix 0)

example : ¬ incompatibleTree.DimensionCompatible incompatibleDimensions := by
  simp [incompatibleTree, incompatibleDimensions, Parenthesization.DimensionCompatible,
    Parenthesization.rows, Parenthesization.cols]
  change ¬ 4 = 2
  decide

example : ¬ incompatibleTree.IsValid incompatibleDimensions := by
  intro h
  exact (show ¬ incompatibleTree.DimensionCompatible incompatibleDimensions by
    simp [incompatibleTree, incompatibleDimensions, Parenthesization.DimensionCompatible,
      Parenthesization.rows, Parenthesization.cols]
    change ¬ 4 = 2
    decide) h.2

private def largeDimensions : Vector Nat 3 :=
  #v[10000000000, 10000000000, 10000000000]

#guard (matrixChainOrder largeDimensions (by decide)).ret.optimalCost ==
  1000000000000000000000000000000

private def figureDimensions : Vector Nat 7 := #v[30, 35, 15, 5, 10, 20, 25]

private def figureTree : Parenthesization 6 :=
  .multiply
    (.multiply (.matrix 0) (.multiply (.matrix 1) (.matrix 2)))
    (.multiply (.multiply (.matrix 3) (.matrix 4)) (.matrix 5))

#guard (matrixChainOrder figureDimensions (by decide)).ret ==
  ({ optimalCost := 15125, parenthesization := figureTree } : Result 6)

#guard (matrixChainOrder figureDimensions (by decide)).time ==
  { candidateEvaluations := 35, reconstructionNodes := 11 }

#guard (matrixChainOrder figureDimensions (by decide)).time.total == 46

private def exerciseDimensions : Vector Nat 7 := #v[5, 10, 3, 12, 5, 50, 6]

private def exerciseTree : Parenthesization 6 :=
  .multiply
    (.multiply (.matrix 0) (.matrix 1))
    (.multiply (.multiply (.matrix 2) (.matrix 3)) (.multiply (.matrix 4) (.matrix 5)))

#guard (matrixChainOrder exerciseDimensions (by decide)).ret ==
  ({ optimalCost := 2010, parenthesization := exerciseTree } : Result 6)

example : (matrixChainOrder figureDimensions (by decide)).ret.parenthesization.IsValid
    figureDimensions := matrixChainOrder_parenthesization_valid figureDimensions (by decide)

example : scalarMultiplicationCost figureDimensions
      (matrixChainOrder figureDimensions (by decide)).ret.parenthesization =
    (matrixChainOrder figureDimensions (by decide)).ret.optimalCost :=
  matrixChainOrder_cost_eq figureDimensions (by decide)

section GenericClients

variable {n : Nat} (dimensions : Vector Nat (n + 1)) (hn : 0 < n)

example : (matrixChainOrder dimensions hn).ret.parenthesization.IsValid dimensions :=
  matrixChainOrder_parenthesization_valid dimensions hn

example : scalarMultiplicationCost dimensions
      (matrixChainOrder dimensions hn).ret.parenthesization =
    (matrixChainOrder dimensions hn).ret.optimalCost :=
  matrixChainOrder_cost_eq dimensions hn

example (tree : Parenthesization n) (hTree : tree.IsValid dimensions) :
    (matrixChainOrder dimensions hn).ret.optimalCost ≤
      scalarMultiplicationCost dimensions tree :=
  matrixChainOrder_minimal dimensions hn tree hTree

example : (matrixChainOrder dimensions hn).time.candidateEvaluations =
    Nat.choose (n + 1) 3 := matrixChainOrder_candidateEvaluations dimensions hn

example : (matrixChainOrder dimensions hn).time.reconstructionNodes = 2 * n - 1 :=
  matrixChainOrder_reconstructionNodes dimensions hn

example : (matrixChainOrder dimensions hn).time.total =
    Nat.choose (n + 1) 3 + (2 * n - 1) := matrixChainOrder_time dimensions hn

example : (matrixChainOrder dimensions hn).time.total ≤ 3 * n ^ 3 :=
  matrixChainOrder_time_le_three_mul_cube dimensions hn

end GenericClients

end Cslib.Algorithms.Lean.MatrixChainTests
