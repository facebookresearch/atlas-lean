/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
public meta import CSLibExt.Complexity.Algebraic.ArithmeticCircuit
public meta import CSLibExt.Complexity.Algebraic.MatrixMultiplication
import Mathlib.Algebra.Field.ULift
import Mathlib.Data.Rat.Defs
public meta import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-! # Actual arithmetic-circuit and rectangular-exponent tests -/

namespace Cslib.Complexity.Algebraic.RectangularCircuitExponentTests

open Cslib.Complexity.Algebraic MatrixMultiplicationExponent

private def actualA : Matrix (Fin 2) (Fin 1) ℚ := fun i _ => if i = 0 then 2 else -3
private def actualB : Matrix (Fin 1) (Fin 3) ℚ := fun _ j =>
  if j = 0 then 5 else if j = 1 then 0 else -7

example : (outerMatrixCircuit ℚ 2 3).evaluate (matrixInput actualA actualB) (0, 2) = -14 := by
  rw [outerMatrixCircuit_correct 2 3]
  norm_num [actualA, actualB, Matrix.mul_apply]

example {c : MatrixArithmeticCircuit ℚ 2 1 3} (h : IsMatrixMultiplication c) : 6 ≤ c.size :=
  h.output_cost_le 0

example : (outerMatrixCircuit ℚ 2 3).size = 6 := rfl

#eval List.ofFn fun i : Fin 6 =>
  (outerMatrixCircuit ℚ 2 3).evaluate (matrixInput actualA actualB) (finProdFinEquiv.symm i)

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private def binaryA : Matrix (Fin 2) (Fin 1) (ZMod 2) := fun i _ => if i = 0 then 1 else 0
private def binaryB : Matrix (Fin 1) (Fin 2) (ZMod 2) := fun _ _ => 1

example : (outerMatrixCircuit (ZMod 2) 2 2).evaluate (matrixInput binaryA binaryB) (1, 0) = 0 := by
  rw [outerMatrixCircuit_correct 2 2]
  rfl

example (x : ZMod 2) : x * x = x := by
  fin_cases x
  · change (0 : ZMod 2) * 0 = 0
    simp
  · change (1 : ZMod 2) * 1 = 1
    simp

#eval List.ofFn fun i : Fin 4 =>
  (outerMatrixCircuit (ZMod 2) 2 2).evaluate
    (matrixInput binaryA binaryB) (finProdFinEquiv.symm i)

private def dotTwo : MatrixArithmeticCircuit ℚ 1 2 1 where
  size := 3
  gate i := if h0 : i.val = 0 then
    .mul (.input (.inl (0, 0))) (.input (.inr (0, 0)))
    else if h1 : i.val = 1 then
      .mul (.input (.inl (0, 1))) (.input (.inr (1, 0)))
    else .add (.node ⟨0, by omega⟩) (.node ⟨1, by omega⟩)
  output _ := .node 2

example : IsMatrixMultiplication dotTwo := by
  intro A B i j
  fin_cases i
  fin_cases j
  simp [dotTwo, ArithmeticCircuit.evaluate, ArithmeticCircuit.evaluateNode,
    ArithmeticGate.evaluate, ArithmeticOperand.evaluate, matrixInput, Matrix.mul_apply,
    Fin.sum_univ_two]

private def dotA : Matrix (Fin 1) (Fin 2) ℚ := fun _ k => if k = 0 then 2 else 3
private def dotB : Matrix (Fin 2) (Fin 1) ℚ := fun k _ => if k = 0 then 5 else -7

#eval dotTwo.evaluate (matrixInput dotA dotB) (0, 0)

example : dotTwo.size = 3 := rfl

private def scalarSubtraction : ArithmeticCircuit ℚ (Fin 2) Unit where
  size := 2
  gate i := if h : i.val = 0 then .mul (.input 0) (.input 1)
    else .sub (.node ⟨0, by omega⟩) (.constant 5)
  output _ := .node 1

#eval scalarSubtraction.evaluate (fun i => if i = 0 then 2 else 3) ()

example : rectangularCircuitExponent ℚ 0 = 2 := rectangularCircuitExponent_zero ℚ
example : rectangularCircuitExponent (ZMod 2) 0 = 2 := rectangularCircuitExponent_zero (ZMod 2)
example : rectangularCircuitExponent (ULift.{2} ℚ) 0 = 2 :=
  rectangularCircuitExponent_zero (ULift.{2} ℚ)

example : HasRectangularCircuitExponent ℚ 0 (rectangularCircuitExponent ℚ 0).toReal := by
  apply rectangularCircuitExponent_endpoint ℚ (by norm_num)
  rw [rectangularCircuitExponent_zero]
  simp

example (k : ℝ) : 2 ≤ rectangularCircuitExponent ℚ k := two_le_rectangularCircuitExponent ℚ k

example : HasTensorRankAtMost (matrixMultiplicationStructureTensor ℚ 2 3 4) 24 := by
  simpa using matrixMultiplicationStructureTensor_rank_le_product ℚ 2 3 4

example (A : Matrix (Fin 2) (Fin 3) ℚ) (B : Matrix (Fin 3) (Fin 4) ℚ)
    (i : Fin 2) (j : Fin 4) :
    matrixMultiplicationTensorContraction ℚ A B i j = (A * B) i j :=
  matrixMultiplicationTensorContraction_eq_mul ℚ A B i j

example : rectangularInnerDimension 5 1 = 5 := by simp

example : squareMatrixMultiplicationCircuitExponent ℚ = rectangularCircuitExponent ℚ 1 :=
  rfl

example : 2 ≤ squareMatrixMultiplicationCircuitExponent ℚ :=
  two_le_squareMatrixMultiplicationCircuitExponent ℚ

example : 2 ≤ squareMatrixMultiplicationCircuitExponent (ZMod 2) :=
  two_le_squareMatrixMultiplicationCircuitExponent (ZMod 2)

example {w : ℝ} (hw : 0 ≤ w) :
    squareMatrixMultiplicationCircuitExponent ℚ ≤ ENNReal.ofReal w ↔
      HasRectangularCircuitExponent ℚ 1 w :=
  squareMatrixMultiplicationCircuitExponent_le_iff ℚ hw

example (hfinite : squareMatrixMultiplicationCircuitExponent ℚ ≠ ⊤) :
    HasRectangularCircuitExponent ℚ 1
      (squareMatrixMultiplicationCircuitExponent ℚ).toReal :=
  squareMatrixMultiplicationCircuitExponent_endpoint ℚ hfinite

#eval "C15B_ACTUAL_CIRCUIT_INPUTS_EXECUTED"

end Cslib.Complexity.Algebraic.RectangularCircuitExponentTests
