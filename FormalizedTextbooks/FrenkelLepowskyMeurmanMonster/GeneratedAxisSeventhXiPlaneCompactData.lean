/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneLiftData

/-! The compact exact binary relabeling and quadratic sign of the source permutation word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The literal forward matrix, with the source masks interpreted as binary columns. -/
def generatedSeventhXiPlaneCodeMatrix : Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j =>
  golayLabelCoefficients
    ⟨generatedSeventhXiPlaneCodeColumns j % 4096, Nat.mod_lt _ (by decide)⟩ i

/-- The literal inverse matrix of the same exact relabeling. -/
def generatedSeventhXiPlaneCodeInverseMatrix : Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j =>
  golayLabelCoefficients
    ⟨generatedSeventhXiPlaneCodeInverseColumns j % 4096, Nat.mod_lt _ (by decide)⟩ i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Finite inverse matrices and complete central-phase basis images are checked in the kernel.
/-- The ordinary kernel verifies both inverse laws of the compact binary matrices. -/
theorem generatedSeventhXiPlaneCode_inverse :
    generatedSeventhXiPlaneCodeInverseMatrix * generatedSeventhXiPlaneCodeMatrix = 1 ∧
      generatedSeventhXiPlaneCodeMatrix * generatedSeventhXiPlaneCodeInverseMatrix = 1 := by
  decide +kernel

/-- The exact binary spin-label equivalence defined by the checked inverse matrices. -/
def generatedSeventhXiPlaneCode : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun := generatedSeventhXiPlaneCodeMatrix.mulVec
  invFun := generatedSeventhXiPlaneCodeInverseMatrix.mulVec
  left_inv x := by
    rw [Matrix.mulVec_mulVec, generatedSeventhXiPlaneCode_inverse.1, Matrix.one_mulVec]
  right_inv x := by
    rw [Matrix.mulVec_mulVec, generatedSeventhXiPlaneCode_inverse.2, Matrix.one_mulVec]
  map_add' := Matrix.mulVec_add _
  map_smul' a x := by
    exact Matrix.mulVec_smul _ a x

/-- The compact source phase matrix, with the original central sign coefficients retained. -/
def generatedSeventhXiPlanePhase : Fin 12 → Fin 12 → ZMod 2 := fun i j =>
  golayBooleanCast ((generatedSeventhXiPlanePhaseRows i).testBit j.val)

/-- The actual orthogonal spin normalizer from the compact relabeling and quadratic sign. -/
noncomputable def generatedSeventhXiPlaneCompactSpin : SpinHolomorph :=
  monsterMonomialPermutationHolomorph generatedSeventhXiPlaneCode *
    monsterMonomialDiagonalHolomorph generatedSeventhXiPlanePhase

/-- The full coefficient-retaining compact Q image. -/
def generatedSeventhXiPlaneCompactImage (q : Q) : Q :=
  monsterMonomialPermutationImage generatedSeventhXiPlaneCode
    (monsterMonomialDiagonalImage generatedSeventhXiPlanePhase q)

/-- The compact image is the genuine conjugation action of this orthogonal spin operator. -/
theorem generatedSeventhXiPlaneCompactSpin_conjugation (q : Q) :
    spinConjugation generatedSeventhXiPlaneCompactSpin q =
      generatedSeventhXiPlaneCompactImage q := by
  rw [generatedSeventhXiPlaneCompactSpin, map_mul]
  change spinConjugation (monsterMonomialPermutationHolomorph generatedSeventhXiPlaneCode)
    (spinConjugation (monsterMonomialDiagonalHolomorph generatedSeventhXiPlanePhase) q) = _
  rw [monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Finite inverse matrices and complete central-phase basis images are checked in the kernel.
/-- All twenty-four full compact images agree with the final literal source states. -/
theorem generatedSeventhXiPlaneCompactImage_basis : ∀ j : Fin 24,
    toAdd (generatedSeventhXiPlaneCompactImage (xiSpinBinaryBasisLift j)).base =
      toAdd (generatedSeventhXiPlaneQState 13 j).base ∧
    toAdd (generatedSeventhXiPlaneCompactImage (xiSpinBinaryBasisLift j)).coeff =
      toAdd (generatedSeventhXiPlaneQState 13 j).coeff := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
