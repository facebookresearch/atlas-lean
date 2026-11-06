/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bitwise labels for the original seventh-axis compact spin relabeling. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneIntegerSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The twelve integer column masks of each actual compact binary permutation. -/
def generatedSeventhXiPlaneBitCodeColumns (k : Fin 2) : Fin 12 → ℕ :=
  if k = 0 then generatedSeventhXiPlaneCodeColumns else generatedSeventhXiPlaneCodeInverseColumns

/-- Exact row masks of the same forward and inverse source matrices. -/
def generatedSeventhXiPlaneBitCodeRows : Fin 2 → Fin 12 → ℕ :=
  ![![2032, 1277, 390, 882, 209, 713, 1465, 504, 355, 570, 1547, 3087],
    ![143, 1038, 1021, 439, 1239, 1598, 1065, 97, 1942, 1360, 1126, 2733]]

/-- The actual forward or inverse compact source code equivalence. -/
def generatedSeventhXiPlaneBitCode (k : Fin 2) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  if k = 0 then generatedSeventhXiPlaneCode else generatedSeventhXiPlaneCode.symm

private theorem rows_matrix :
    (fun (i j : Fin 12) =>
      golayBooleanCast ((generatedSeventhXiPlaneBitCodeRows 0 i).testBit j.val)) =
      generatedSeventhXiPlaneCodeMatrix ∧
    (fun (i j : Fin 12) =>
      golayBooleanCast ((generatedSeventhXiPlaneBitCodeRows 1 i).testBit j.val)) =
      generatedSeventhXiPlaneCodeInverseMatrix := by
  decide +kernel

private theorem generatedSeventhXiPlaneBitCode_apply (k : Fin 2) (t : SpinIndex) :
    generatedSeventhXiPlaneBitCode k t =
      (fun (i j : Fin 12) =>
        golayBooleanCast ((generatedSeventhXiPlaneBitCodeRows k i).testBit j.val)) *ᵥ t := by
  fin_cases k
  · change generatedSeventhXiPlaneCodeMatrix *ᵥ t = _
    exact congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M.mulVec t)
      rows_matrix.1.symm
  · change generatedSeventhXiPlaneCodeInverseMatrix *ᵥ t = _
    exact congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => M.mulVec t)
      rows_matrix.2.symm

/-- The actual binary permutation evaluated through twelve selected column xors. -/
def generatedSeventhXiPlaneBitCodeLabel (k : Fin 2) (n : Fin 4096) : Fin 4096 :=
  ⟨((if n.val.testBit 0 then generatedSeventhXiPlaneBitCodeColumns k 0 else 0) ^^^
    (if n.val.testBit 1 then generatedSeventhXiPlaneBitCodeColumns k 1 else 0) ^^^
    (if n.val.testBit 2 then generatedSeventhXiPlaneBitCodeColumns k 2 else 0) ^^^
    (if n.val.testBit 3 then generatedSeventhXiPlaneBitCodeColumns k 3 else 0) ^^^
    (if n.val.testBit 4 then generatedSeventhXiPlaneBitCodeColumns k 4 else 0) ^^^
    (if n.val.testBit 5 then generatedSeventhXiPlaneBitCodeColumns k 5 else 0) ^^^
    (if n.val.testBit 6 then generatedSeventhXiPlaneBitCodeColumns k 6 else 0) ^^^
    (if n.val.testBit 7 then generatedSeventhXiPlaneBitCodeColumns k 7 else 0) ^^^
    (if n.val.testBit 8 then generatedSeventhXiPlaneBitCodeColumns k 8 else 0) ^^^
    (if n.val.testBit 9 then generatedSeventhXiPlaneBitCodeColumns k 9 else 0) ^^^
    (if n.val.testBit 10 then generatedSeventhXiPlaneBitCodeColumns k 10 else 0) ^^^
    (if n.val.testBit 11 then generatedSeventhXiPlaneBitCodeColumns k 11 else 0)) % 4096,
    Nat.mod_lt _ (by norm_num)⟩

private def bin (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bin_xor (a b : Bool) : bin (Bool.xor a b) = bin a + bin b := by
  cases a <;> cases b <;> decide

private theorem selected_bit (n : Fin 4096) (m : ℕ) (j : ℕ) (i : Fin 12) :
    bin ((if n.val.testBit j then m else 0).testBit i.val) =
      bin (n.val.testBit j) * bin (m.testBit i.val) := by
  cases h : n.val.testBit j <;> simp [bin]

private theorem columns_actual (k : Fin 2) (i j : Fin 12) :
    (generatedSeventhXiPlaneBitCodeRows k i).testBit j.val =
      (generatedSeventhXiPlaneBitCodeColumns k j).testBit i.val := by
  revert k i j
  decide +kernel

set_option maxHeartbeats 1000000 in
-- Expand the twelve packed column terms before identifying their binary matrix coefficients.
/-- The column-xor evaluator is exactly the actual permutation on every spin label. -/
theorem generatedSeventhXiPlaneBitCodeLabel_actual (k : Fin 2) (n : Fin 4096) :
    nortonUIntegerLabel (generatedSeventhXiPlaneBitCode k (golayLabelCoefficients n)) =
      generatedSeventhXiPlaneBitCodeLabel k n := by
  apply golayLabelCoefficients_injective
  rw [nortonUIntegerLabel_inverse]
  funext i
  rw [generatedSeventhXiPlaneBitCode_apply, Matrix.mulVec, dotProduct]
  change (∑ j : Fin 12, bin ((generatedSeventhXiPlaneBitCodeRows k i).testBit j.val) *
    bin (n.val.testBit j.val)) = bin
      ((((if n.val.testBit 0 then generatedSeventhXiPlaneBitCodeColumns k 0 else 0) ^^^
    (if n.val.testBit 1 then generatedSeventhXiPlaneBitCodeColumns k 1 else 0) ^^^
    (if n.val.testBit 2 then generatedSeventhXiPlaneBitCodeColumns k 2 else 0) ^^^
    (if n.val.testBit 3 then generatedSeventhXiPlaneBitCodeColumns k 3 else 0) ^^^
    (if n.val.testBit 4 then generatedSeventhXiPlaneBitCodeColumns k 4 else 0) ^^^
    (if n.val.testBit 5 then generatedSeventhXiPlaneBitCodeColumns k 5 else 0) ^^^
    (if n.val.testBit 6 then generatedSeventhXiPlaneBitCodeColumns k 6 else 0) ^^^
    (if n.val.testBit 7 then generatedSeventhXiPlaneBitCodeColumns k 7 else 0) ^^^
    (if n.val.testBit 8 then generatedSeventhXiPlaneBitCodeColumns k 8 else 0) ^^^
    (if n.val.testBit 9 then generatedSeventhXiPlaneBitCodeColumns k 9 else 0) ^^^
    (if n.val.testBit 10 then generatedSeventhXiPlaneBitCodeColumns k 10 else 0) ^^^
    (if n.val.testBit 11 then generatedSeventhXiPlaneBitCodeColumns k 11 else 0)) % 4096).testBit
        i.val)
  rw [Nat.testBit_mod_two_pow _ 12 i.val]
  have hi : decide (i.val < 12) = true := decide_eq_true_eq.mpr i.isLt
  simp only [hi, Bool.true_and]
  simp_rw [Nat.testBit_xor, bin_xor]
  simp_rw [selected_bit]
  simp_rw [columns_actual]
  norm_num [Fin.sum_univ_succ]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
