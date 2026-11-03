/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.TensorNetwork.GridTranspose

namespace TensorNetwork

variable {ρ γ A : Type*}

private def rectangularLabeling :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) Nat :=
  fun w w' => if w = w' then w.1.val else 9

private def rectangularTensor : Instance (Fin 2 × Fin 3) Nat := fun w h =>
  if h = rectangularLabeling w then 1 + w.1.val + 2 * w.2.val else 0

private def rectangularKernel
    (ω : ((Fin 2 × Fin 2) × (Fin 3 × Fin 3))) (_ _ _ _ : Nat) : ℤ :=
  1 + ω.2.1.val + ω.2.2.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem rectangularGridValue :
    gridValue {9} {0, 1} rectangularTensor rectangularKernel = 17280 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private example :
    gridValue {9} {0, 1} rectangularTensor.transpose
      (transposeRectangleKernel rectangularKernel) = 17280 := by
  rw [gridValue_transpose]
  exact rectangularGridValue

private def orientedLabeling : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Nat := fun w w' =>
  if w = (0, 0) ∧ w' = (1, 1) then 1
  else if w = (1, 0) ∧ w' = (0, 1) then 1
  else 0

private def vertexWeight (w : Fin 2 × Fin 2) : ℤ :=
  if w = (0, 0) then 2
  else if w = (0, 1) then 3
  else if w = (1, 0) then 5
  else 7

private def orientedTensor : Instance (Fin 2 × Fin 2) Nat := fun w h =>
  if h = orientedLabeling w then vertexWeight w else 0

private def orientedKernel (x y u v : Nat) : ℤ :=
  x + 2 * y + 4 * u + 8 * v

private example :
    rectangleApply orientedKernel orientedLabeling (((0, 1), (0, 1))) = 5 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem orientedGridValue :
    gridValue {0, 1} {0} orientedTensor (fun _ => orientedKernel) = 1050 := by
  decide

private example :
    gridValue {0, 1} {0} orientedTensor.transpose
      (transposeRectangleKernel (fun _ => orientedKernel)) = 1050 := by
  rw [gridValue_transpose]
  exact orientedGridValue

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private example :
    gridValue {0, 1} {0} orientedTensor.transpose
      (fun _ x y u v => orientedKernel x y u v) = 630 := by
  decide

private def zeroTensor {J : Type*} : Instance J Nat := fun _ _ => 0

private example :
    gridValue {0} {0} (zeroTensor (J := Fin 2 × Fin 3))
      (fun _ _ _ _ _ => 1) = 0 := by
  decide

private def emptyRowTensor : Instance (Fin 0 × Fin 2) Nat := fun w => Fin.elim0 w.1

private example :
    gridValue ∅ ∅ emptyRowTensor.transpose (transposeRectangleKernel fun _ _ _ _ _ => 0) = 1 := by
  decide

private def emptyColumnTensor : Instance (Fin 2 × Fin 0) Nat := fun w => Fin.elim0 w.2

private example :
    gridValue ∅ ∅ emptyColumnTensor.transpose
      (transposeRectangleKernel fun _ _ _ _ _ => 0) = 1 := by
  decide

private def oneTensor {J : Type*} : Instance J Nat := fun _ _ => 1

private example :
    gridValue ∅ {0} (oneTensor (J := Fin 1 × Fin 2)).transpose
      (transposeRectangleKernel fun _ _ _ _ _ => 1) = 0 := by
  decide

private example :
    gridValue {0} ∅ (oneTensor (J := Fin 1 × Fin 1)).transpose
      (transposeRectangleKernel fun _ _ _ _ _ => 1) = 0 := by
  decide

private example (R : Instance (Fin 2 × Fin 3) Nat) : R.transpose.transpose = R := by
  simp

private example
    (G : ((Fin 2 × Fin 2) × (Fin 3 × Fin 3)) → Nat → Nat → Nat → Nat → ℤ) :
    transposeRectangleKernel (transposeRectangleKernel G) = G := by
  simp

private def sourceTransposeInstance (R : Instance (ρ × γ) A) : Instance (γ × ρ) A :=
  fun w h => R w.swap fun w' => h w'.swap

private def sourceTransposeKernel
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    ((γ × γ) × (ρ × ρ)) → A → A → A → A → ℤ :=
  fun ω x y u v => G (ω.2, ω.1) x u y v

private def sourceTransposeLabeling (ρ γ A : Type*) :
    Matrix (ρ × γ) (ρ × γ) A ≃ Matrix (γ × ρ) (γ × ρ) A :=
  (Equiv.prodComm ρ γ).arrowCongr
    ((Equiv.prodComm ρ γ).arrowCongr (Equiv.refl A))

private example (R : Instance (ρ × γ) A) : sourceTransposeInstance R = R.transpose := rfl

private example
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    sourceTransposeKernel G = transposeRectangleKernel G := rfl

private example (ℓ : Matrix (ρ × γ) (ρ × γ) A) (w w' : γ × ρ) :
    sourceTransposeLabeling ρ γ A ℓ w w' = ℓ w.swap w'.swap := by
  rfl

private example [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
    [Fintype A] [DecidableEq A] (R : Instance (ρ × γ) A)
    (G : ((ρ × ρ) × (γ × γ)) → A → A → A → A → ℤ) :
    gridValue Finset.univ Finset.univ (sourceTransposeInstance R) (sourceTransposeKernel G) =
      gridValue Finset.univ Finset.univ R G := by
  change gridValue Finset.univ Finset.univ R.transpose (transposeRectangleKernel G) =
    gridValue Finset.univ Finset.univ R G
  exact gridValue_transpose Finset.univ Finset.univ R G

#print axioms Instance.transpose
#print axioms Instance.transpose_apply
#print axioms Instance.transpose_transpose
#print axioms transposeRectangleKernel
#print axioms transposeRectangleKernel_apply
#print axioms transposeRectangleKernel_transposeRectangleKernel
#print axioms gridValue_transpose

end TensorNetwork
