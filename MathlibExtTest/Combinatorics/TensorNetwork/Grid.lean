/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.Grid
import Mathlib.Tactic.FinCases

namespace TensorNetwork

open Finset

private def sourceGridValue {ρ γ A : Type*} [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [Fintype A] [DecidableEq A]
    (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) : ℤ :=
  ∑ ℓ : Matrix (ρ × γ) (ρ × γ) A,
    (∏ w, R w (ℓ w)) *
      ((∏ a, ∏ q ∈ orderedPairs γ,
          if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
        (∏ i, ∏ p ∈ orderedPairs ρ,
          if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
        ∏ ω ∈ gridRectangles ρ γ, rectangleApply (G ω) ℓ ω)

private example {ρ γ A : Type*} [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] [Fintype A] [DecidableEq A]
    (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    sourceGridValue R G = gridValue univ univ R G := by
  simp [sourceGridValue, gridValue, gridLabelings]

def oneVertexWeights : Instance (Fin 1 × Fin 1) Nat := fun w h =>
  if h w = 2 then 2 else if h w = 5 then 5 else 0

example : gridValue ∅ {2, 5} oneVertexWeights (fun _ _ _ _ _ => 1) = 7 := by
  decide

example :
    gridValue ∅ {2, 5} (oneVertexWeights.onGrid 2 (Equiv.refl _))
      (fun _ _ _ _ _ => 1) = 2 := by
  decide

def defaultOutsideEdgeWeights : Instance (Fin 1 × Fin 1) Nat := fun w h =>
  if h w = 7 then 13 else 17

example :
    gridValue {2, 3} {7, 11}
      (defaultOutsideEdgeWeights.onGrid 7 (Equiv.refl _))
      (fun _ _ _ _ _ => 1) = 13 := by
  decide

def orientedLabeling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Nat := fun w w' =>
  if w = (0, 0) ∧ w' = (1, 1) then 1
  else if w = (1, 0) ∧ w' = (0, 1) then 1
  else 0

def vertexWeight (w : Fin 2 × Fin 2) : ℤ :=
  if w = (0, 0) then 2
  else if w = (0, 1) then 3
  else if w = (1, 0) then 5
  else 7

def orientedTensor : Instance (Fin 2 × Fin 2) Nat := fun w h =>
  if h = orientedLabeling w then vertexWeight w else 0

example : orientedLabeling ∈ gridLabelings {0, 1} {0} := by
  rw [mem_gridLabelings]
  rintro ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;> decide

def orientedKernel (x y u v : Nat) : ℤ :=
  x + 2 * y + 4 * u + 8 * v

example :
    rectangleApply orientedKernel orientedLabeling (((0, 1), (0, 1))) = 5 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
example : gridValue {0, 1} {0} orientedTensor (fun _ => orientedKernel) = 1050 := by
  decide

def crossingLabeling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Nat := fun w w' =>
  if w = w' then 7
  else if (w = (0, 0) ∧ w' = (1, 1)) ∨ (w = (1, 1) ∧ w' = (0, 0)) then 1
  else 0

def crossingTensor : Instance (Fin 2 × Fin 2) Nat := fun w h =>
  if h = crossingLabeling w then vertexWeight w else 0

def finFourGrid : Fin 4 ≃ Fin 2 × Fin 2 :=
  (finProdFinEquiv (m := 2) (n := 2)).symm

def crossingSource : Instance (Fin 4) Nat := fun v h =>
  crossingTensor (finFourGrid v) (fun w => h (finFourGrid.symm w))

example : crossingSource.value {0, 1} 7 = 210 := by
  decide

example :
    gridValue {0, 1} {7, 11} (crossingSource.onGrid 7 finFourGrid)
      (fun _ => crossing) = 210 := by
  rw [← crossingSource.value_eq_gridValue_crossing {0, 1} {7, 11} 7 (by simp)
    finFourGrid]
  decide

example :
    crossingSource.value {0, 1} 7 =
      gridValue {0, 1} {7, 11} (crossingSource.onGrid 7 finFourGrid)
        (fun _ => crossing) := by
  exact crossingSource.value_eq_gridValue_crossing {0, 1} {7, 11} 7 (by simp)
    finFourGrid

def zeroVertexTensor : Instance (Fin 1 × Fin 1) Nat := fun _ _ => 0

example : gridValue {0} {0} zeroVertexTensor (fun _ _ _ _ _ => 1) = 0 := by
  decide

def emptyRowTensor : Instance (Fin 0 × Fin 2) Nat := fun w => Fin.elim0 w.1

example : gridValue ∅ ∅ emptyRowTensor (fun _ _ _ _ _ => 0) = 1 := by
  decide

def emptyColumnTensor : Instance (Fin 2 × Fin 0) Nat := fun w => Fin.elim0 w.2

example : gridValue ∅ ∅ emptyColumnTensor (fun _ _ _ _ _ => 0) = 1 := by
  decide

def nonemptyTensor {ρ γ : Type*} : Instance (ρ × γ) Nat := fun _ _ => 1

example :
    gridValue ∅ {0} (nonemptyTensor (ρ := Fin 1) (γ := Fin 2))
      (fun _ _ _ _ _ => 1) = 0 := by
  decide

example :
    gridValue {0} ∅ (nonemptyTensor (ρ := Fin 1) (γ := Fin 1))
      (fun _ _ _ _ _ => 1) = 0 := by
  decide

example : (gridRectangles (Fin 2) (Fin 3)).card = 3 := by
  decide

example {ρ γ : Type*} [Fintype ρ] [LinearOrder ρ]
    [Fintype γ] [LinearOrder γ] :
    (gridRectangles ρ γ).card =
      (Fintype.card ρ).choose 2 * (Fintype.card γ).choose 2 := by
  exact card_gridRectangles

#print axioms gridRectangles
#print axioms rectangleApply
#print axioms gridLabelings
#print axioms mem_gridLabelings
#print axioms gridValue
#print axioms Instance.onGrid
#print axioms crossing
#print axioms Instance.value_eq_gridValue_crossing
#print axioms card_gridRectangles

end TensorNetwork
