/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisCertificate3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisCertificate4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisCertificate5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisExt

/-! Full-phase matrices equal the actual corrected spin conjugation on every element of Q. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All twenty-four original corrected basis images, including their central coefficients. -/
theorem generatedFourth_lift_short_basis_certificate (j : Fin 24) :
    toAdd (generatedFourthLiftShortQFast (xiSpinBinaryBasisLift j)).base =
        generatedFourthLiftQBinaryMatrix.col j ∧
      toAdd (generatedFourthLiftShortQFast (xiSpinBinaryBasisLift j)).coeff =
        generatedFourthLiftQPhaseMatrix j j := by
  by_cases h0 : j.val < 4
  · have he : (⟨0 + (j.val - 0), by omega⟩ : Fin 24) = j := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using generatedFourth_lift_short_basis_certificate_0
      (⟨j.val - 0, by omega⟩ : Fin 4)
  by_cases h1 : j.val < 8
  · have he : (⟨4 + (j.val - 4), by omega⟩ : Fin 24) = j := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using generatedFourth_lift_short_basis_certificate_1
      (⟨j.val - 4, by omega⟩ : Fin 4)
  by_cases h2 : j.val < 12
  · have he : (⟨8 + (j.val - 8), by omega⟩ : Fin 24) = j := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using generatedFourth_lift_short_basis_certificate_2
      (⟨j.val - 8, by omega⟩ : Fin 4)
  by_cases h3 : j.val < 16
  · have he : (⟨12 + (j.val - 12), by omega⟩ : Fin 24) = j := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using generatedFourth_lift_short_basis_certificate_3
      (⟨j.val - 12, by omega⟩ : Fin 4)
  by_cases h4 : j.val < 20
  · have he : (⟨16 + (j.val - 16), by omega⟩ : Fin 24) = j := by
      apply Fin.ext; dsimp; omega
    simpa only [he] using generatedFourth_lift_short_basis_certificate_4
      (⟨j.val - 16, by omega⟩ : Fin 4)
  have he : (⟨20 + (j.val - 20), by omega⟩ : Fin 24) = j := by
    apply Fin.ext; dsimp; omega
  simpa only [he] using generatedFourth_lift_short_basis_certificate_5
    (⟨j.val - 20, by omega⟩ : Fin 4)

/-- Evaluation of the certified homomorphism, without unfolding its cocycle proof. -/
theorem generatedFourth_lift_short_matrix_value (q : Q) :
    generatedFourthLiftShortMatrixHom q =
      ⟨ofAdd (generatedFourthLiftQBinaryMatrix *ᵥ toAdd q.base),
        ofAdd (toAdd q.coeff + generatedFourthLiftQMatrixPhase
          generatedFourthLiftQPhaseMatrix (toAdd q.base))⟩ := rfl

/-- The original spin conjugation has the certified literal binary and central matrices. -/
theorem generatedFourth_lift_short_matrix_hom :
    (spinConjugation generatedFourthFlagCorrectedLift.val.1).toMonoidHom =
      generatedFourthLiftShortMatrixHom := by
  apply generatedFourth_lift_q_hom_ext
  · intro j
    have hc := generatedFourth_lift_short_basis_certificate j
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change toAdd (spinConjugation generatedFourthFlagCorrectedLift.val.1
        (xiSpinBinaryBasisLift j)).base = _
      rw [generatedFourth_lift_corrected_q_image, generatedFourth_lift_short_q_fast]
      rw [generatedFourth_lift_short_matrix_value]
      simpa only [xiSpinBinaryBasisLift, toAdd_ofAdd, Matrix.mulVec_single_one] using hc.1
    · apply toAdd.injective
      change toAdd (spinConjugation generatedFourthFlagCorrectedLift.val.1
        (xiSpinBinaryBasisLift j)).coeff = _
      rw [generatedFourth_lift_corrected_q_image, generatedFourth_lift_short_q_fast]
      rw [generatedFourth_lift_short_matrix_value]
      simpa only [xiSpinBinaryBasisLift, toAdd_ofAdd, toAdd_one, zero_add,
        generatedFourthLiftQMatrixPhase, Matrix.toBilin'_single] using hc.2
  · change spinConjugation generatedFourthFlagCorrectedLift.val.1 qCentralInvolution = _
    rw [show qCentralInvolution = qCentral 1 from rfl, spinConjugation_central]
    apply NormalizedCocycleExtension.Extension.ext
    · rw [generatedFourth_lift_short_matrix_value]
      simp [qCentral]
    · rw [generatedFourth_lift_short_matrix_value]
      simp [qCentral, generatedFourthLiftQMatrixPhase]

/-- The certified matrix evaluation is the full genuine preferred-Q image, without phase loss. -/
theorem generatedFourth_lift_short_matrix_action (q : Q) :
    spinConjugation generatedFourthFlagCorrectedLift.val.1 q =
      generatedFourthLiftShortMatrixHom q :=
  DFunLike.congr_fun generatedFourth_lift_short_matrix_hom q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
