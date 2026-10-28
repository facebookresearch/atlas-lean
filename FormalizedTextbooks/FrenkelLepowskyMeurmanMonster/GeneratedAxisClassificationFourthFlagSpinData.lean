/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators

/-! A literal monomial spin lift for the selected flag-correction permutation.
The actual spin conjugation and its binary matrix are verified before any spatial lift is used. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The finite action of the selected permutation on the actual Golay code coefficients. -/
def generatedFourthFlagLiftCodeLabels : Fin 12 → Fin 4096 :=
  ![1, 2, 4, 8, 16, 47, 76, 134, 268, 522, 1055, 2048]

/-- The finite matrix of the selected Golay relabeling. -/
def generatedFourthFlagLiftCodeMatrix : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun i j => golayLabelCoefficients (generatedFourthFlagLiftCodeLabels j) i

/-- The selected relabeling is involutive on the genuine binary labels. -/
theorem generatedFourth_flag_lift_code_square :
    generatedFourthFlagLiftCodeMatrix * generatedFourthFlagLiftCodeMatrix = 1 := by
  decide +kernel

/-- The actual binary linear equivalence of the selected coefficient relabeling. -/
def generatedFourthFlagLiftCode : SpinIndex ≃ₗ[ZMod 2] SpinIndex where
  toFun a := generatedFourthFlagLiftCodeMatrix *ᵥ a
  invFun a := generatedFourthFlagLiftCodeMatrix *ᵥ a
  left_inv a := by
    change generatedFourthFlagLiftCodeMatrix *ᵥ (generatedFourthFlagLiftCodeMatrix *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, generatedFourth_flag_lift_code_square, Matrix.one_mulVec]
  right_inv a := by
    change generatedFourthFlagLiftCodeMatrix *ᵥ (generatedFourthFlagLiftCodeMatrix *ᵥ a) = a
    rw [Matrix.mulVec_mulVec, generatedFourth_flag_lift_code_square, Matrix.one_mulVec]
  map_add' a b := Matrix.mulVec_add _ _ _
  map_smul' c a := Matrix.mulVec_smul _ _ _

/-- A canonical triangular phase shear for the selected compatible binary action. -/
def generatedFourthFlagLiftPhaseRows : Fin 12 → Nat :=
  ![1056, 1696, 1504, 1888, 0, 0, 128, 0, 512, 0, 0, 0]

/-- The exact binary quadratic-sign matrix of this concrete spin lift. -/
def generatedFourthFlagLiftPhase : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => golayBooleanCast ((generatedFourthFlagLiftPhaseRows i).testBit j.val)

/-- An actual element of the spin holomorph with this literal monomial operator. -/
noncomputable def generatedFourthFlagLiftSpin : SpinHolomorph :=
  monsterMonomialPermutationHolomorph generatedFourthFlagLiftCode *
    monsterMonomialDiagonalHolomorph generatedFourthFlagLiftPhase

/-- The full actual Q image, including the chosen quadratic central phase. -/
def generatedFourthFlagLiftQImage (q : Q) : Q :=
  monsterMonomialPermutationImage generatedFourthFlagLiftCode
    (monsterMonomialDiagonalImage generatedFourthFlagLiftPhase q)

/-- The actual spin conjugation retains this exact full-Q image. -/
theorem generatedFourth_flag_lift_spin_conjugation (q : Q) :
    spinConjugation generatedFourthFlagLiftSpin q = generatedFourthFlagLiftQImage q := by
  rw [generatedFourthFlagLiftSpin, map_mul]
  change spinConjugation (monsterMonomialPermutationHolomorph generatedFourthFlagLiftCode)
    (spinConjugation (monsterMonomialDiagonalHolomorph generatedFourthFlagLiftPhase) q) = _
  rw [monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation]
  rfl

/-- The actual quotient action read from these genuine Q conjugations. -/
def generatedFourthFlagLiftBinaryMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => toAdd (generatedFourthFlagLiftQImage (xiSpinBinaryBasisLift j)).base i

/-- The quotient matrix columns are actual spin conjugation columns. -/
theorem generatedFourth_flag_lift_binary_column (j : Fin 24) :
    spinBinaryAction generatedFourthFlagLiftSpin (Pi.single j 1) =
      generatedFourthFlagLiftBinaryMatrix.col j := by
  have h := qBinaryAction_apply (spinConjugation generatedFourthFlagLiftSpin)
    (xiSpinBinaryBasisLift j)
  change spinBinaryAction generatedFourthFlagLiftSpin (Pi.single j 1) =
    toAdd (spinConjugation generatedFourthFlagLiftSpin (xiSpinBinaryBasisLift j)).base at h
  rw [generatedFourth_flag_lift_spin_conjugation] at h
  exact h

/-- Linear extension of the genuine column action. -/
theorem generatedFourth_flag_lift_binary_linear :
    (spinBinaryAction generatedFourthFlagLiftSpin).toLinearMap =
      generatedFourthFlagLiftBinaryMatrix.mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
  intro j
  simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one] using generatedFourth_flag_lift_binary_column j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
