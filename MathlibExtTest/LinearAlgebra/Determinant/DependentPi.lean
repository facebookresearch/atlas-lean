/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Determinant.DependentPi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Unequal dependent product ranks and an empty matrix block

The two product components have ranks one and two, with diagonal eigenvalues
2 and (3,5). Their product determinant is 30. A separate dependent matrix
family has one empty block and one rank-two block; its determinant is 15.
-/

@[expose] public section

noncomputable section
namespace MathlibExtTest.DependentPi

def size : Bool → ℕ
  | false => 1
  | true => 2

abbrev Component (i : Bool) := Fin (size i) → ℚ

def componentMap : (i : Bool) → Component i →ₗ[ℚ] Component i
  | false => Matrix.toLin' (Matrix.diagonal ![(2 : ℚ)])
  | true => Matrix.toLin' (Matrix.diagonal ![(3 : ℚ), 5])

def productMap : (∀ i, Component i) →ₗ[ℚ] ∀ i, Component i :=
  LinearMap.pi fun i => (componentMap i).comp (LinearMap.proj i)

example : LinearMap.dependentPiBlock productMap false true = 0 := by
  ext x j
  simp [LinearMap.dependentPiBlock, productMap]

example :
    LinearMap.dependentPiBlock productMap true true ![(1 : ℚ), 2] = ![(3 : ℚ), 10] := by
  ext j
  fin_cases j <;>
    norm_num [LinearMap.dependentPiBlock, productMap, componentMap, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

theorem product_det : productMap.det = 30 := by
  rw [productMap, LinearMap.det_pi_dependent]
  norm_num [componentMap, Fin.prod_univ_two]

def emptySize : Bool → ℕ
  | false => 0
  | true => 2

def blocks : (i : Bool) → Matrix (Fin (emptySize i)) (Fin (emptySize i)) ℤ
  | false => 0
  | true => Matrix.diagonal ![(3 : ℤ), 5]

example : (Matrix.blockDiagonal' blocks).det = 15 := by
  rw [Matrix.det_blockDiagonal']
  norm_num [blocks, Fin.prod_univ_two]

example :
    Matrix.blockDiagonal' blocks ⟨true, (0 : Fin 2)⟩ ⟨true, (1 : Fin 2)⟩ = 0 := by
  simp [blocks]

example :
    (Matrix.blockDiagonal' (fun i : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℤ))).det = 1 := by
  rw [Matrix.det_blockDiagonal']
  simp

end MathlibExtTest.DependentPi
