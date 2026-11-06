/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhTetradClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightXiMoves
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! The genuine moving Xi sends the original frame to a stated signed tetrad class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original Xi column has two positive and two negative integral coordinates. -/
def leechSeventhXiTetradCoefficients (i : Fin 24) : ℤ :=
  if i = 12 ∨ i = 13 then 1 else if i = 14 ∨ i = 18 then -1 else 0

/-- This stated signed tetrad belongs to the actual source lattice. -/
def leechSeventhXiTetradLattice : leechIntegral :=
  ⟨(4 : ℤ) • leechSeventhXiTetradCoefficients,
    (leechSeventh_four_coordinate_mem_iff _).mpr (by
      unfold leechSeventhXiTetradCoefficients
      decide +kernel)⟩

private theorem integral_double (u : leechIntegral) :
    (2 : ℕ) • (leechIntegralAction generatedSeventhXiPlaneFiber.val.2 u).val =
      generatedSeventhXiPlaneMatrixNumerator *ᵥ u.val := by
  have he := leechIntegralAction_embedding generatedSeventhXiPlaneFiber.val.2 u
  rw [← leechIsomMatrix_mulVec, generatedSeventhXiPlaneFiber_matrix,
    Matrix.smul_mulVec, ← leechCoordinateEmbedding_mulVec] at he
  apply leechCoordinateEmbedding_injective
  rw [map_nsmul, he]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

set_option maxHeartbeats 0 in
-- The original numerator column is checked at each actual coordinate.
private theorem original_column :
    generatedSeventhXiPlaneMatrixNumerator *ᵥ leechCoordinateFrameVector 12 =
      (2 : ℕ) • leechSeventhXiTetradLattice.val := by
  ext i
  fin_cases i <;>
    norm_num [generatedSeventhXiPlaneMatrixNumerator, leechCoordinateFrameVector,
      Matrix.mulVec_single, leechSeventhXiTetradLattice,
      leechSeventhXiTetradCoefficients, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] <;>
    decide +kernel

/-- The original integral spatial action has exactly the stated signed tetrad output. -/
theorem leechSeventhXiTetrad_integral :
    leechIntegralAction generatedSeventhXiPlaneFiber.val.2 (leechCoordinateFrameLattice 12) =
      leechSeventhXiTetradLattice := by
  apply Subtype.ext
  have h := integral_double (leechCoordinateFrameLattice 12)
  rw [show (leechCoordinateFrameLattice 12).val = leechCoordinateFrameVector 12 from rfl,
    original_column] at h
  funext i
  have hi := congrArg (fun v : Fin 24 → ℤ => v i) h
  change 2 * _ = 2 * _ at hi
  exact (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)) hi

/-- All coordinate vectors represent the same original frame class. -/
theorem leechSeventh_coordinate_frame_class (i : Fin 24) :
    leechReduction (leechCoordinateFrameLattice i) =
      leechReduction (leechCoordinateFrameLattice 0) := by
  let w : Fin 24 → ℤ := Pi.single i 1 - Pi.single 0 1
  have hd : (leechCoordinateFrameLattice i).val - (leechCoordinateFrameLattice 0).val =
      (2 : ℤ) • ((4 : ℤ) • w) := by
    ext j
    simp only [leechCoordinateFrameLattice, leechCoordinateFrameVector, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, w, Pi.single_apply]
    split_ifs <;> ring
  apply (leechSeventh_reduction_eq_iff_half _ _ _ hd).mpr
  apply (leechSeventh_four_coordinate_mem_iff w).mpr
  have hs : ∑ j, w j = 0 := by
    simp [w, Finset.sum_sub_distrib, Pi.single_apply]
  rw [hs]
  exact ⟨0, by norm_num⟩

private theorem signed_class :
    leechReduction leechSeventhXiTetradLattice =
      leechSeventhTetradClass (⟨15, by decide +kernel⟩, false) := by
  let w : Fin 24 → ℤ := -Pi.single 14 1 - Pi.single 18 1
  have hd : leechSeventhXiTetradLattice.val -
      (leechSeventhTetradLattice ⟨15, by decide +kernel⟩ false).val =
      (2 : ℤ) • ((4 : ℤ) • w) := by
    ext i
    fin_cases i <;>
      norm_num [leechSeventhXiTetradLattice, leechSeventhXiTetradCoefficients,
        leechSeventhTetradLattice, leechSeventhTetradCoefficients,
        generatedSeventhFiveFrameCoordinates, Pi.single_apply, w]
  apply (leechSeventh_reduction_eq_iff_half _ _ _ hd).mpr
  apply (leechSeventh_four_coordinate_mem_iff w).mpr
  norm_num [w, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Pi.single_apply]

/-- The actual moving spatial Xi sends the distinguished frame to the positive tetrad class. -/
theorem leechSeventhXiTetrad_frame_class :
    leechModTwoAction generatedSeventhXiPlaneFiber.val.2
      (leechReduction (leechCoordinateFrameLattice 0)) =
      leechSeventhTetradClass (⟨15, by decide +kernel⟩, false) := by
  rw [← leechSeventh_coordinate_frame_class 12]
  change leechQuotientAut (leechIntegralAction generatedSeventhXiPlaneFiber.val.2)
    (leechReduction (leechCoordinateFrameLattice 12)) = _
  rw [leechQuotientAut_reduce, leechSeventhXiTetrad_integral]
  exact signed_class

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
