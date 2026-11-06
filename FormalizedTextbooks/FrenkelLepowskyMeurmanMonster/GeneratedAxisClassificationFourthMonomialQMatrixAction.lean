/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQBasisCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQBasisCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQBasisCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQBasisCertificate3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisExt

/-! Certified full extraspecial matrix actions of the four original corrected monomial lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All24 genuine basis images of all four corrected lifts, including the central signs. -/
theorem generatedFourth_monomial_q_basis_certificates (k : Fin 4) (j : Fin 24) :
    toAdd (generatedFourthMonomialCorrectedQImage k (xiSpinBinaryBasisLift j)).base =
      (generatedFourthMonomialQBinaryMatrix k).col j ∧
    toAdd (generatedFourthMonomialCorrectedQImage k (xiSpinBinaryBasisLift j)).coeff =
      generatedFourthMonomialQPhaseMatrix k j j := by
  fin_cases k
  · exact generatedFourth_monomial_q_basis_certificate_0 j
  · exact generatedFourth_monomial_q_basis_certificate_1 j
  · exact generatedFourth_monomial_q_basis_certificate_2 j
  · exact generatedFourth_monomial_q_basis_certificate_3 j

/-- Evaluation of the genuine certified homomorphism without unfolding its cocycle proof. -/
theorem generatedFourth_monomial_q_matrix_value (k : Fin 4) (q : Q) :
    generatedFourthMonomialQMatrixHom k q =
      ⟨ofAdd (generatedFourthMonomialQBinaryMatrix k *ᵥ toAdd q.base),
        ofAdd (toAdd q.coeff + generatedFourthLiftQMatrixPhase
          (generatedFourthMonomialQPhaseMatrix k) (toAdd q.base))⟩ := rfl

/-- The finite checked matrices equal the original spin conjugation on the entire Q group. -/
theorem generatedFourth_monomial_q_matrix_hom (k : Fin 4) :
    (spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1).toMonoidHom =
      generatedFourthMonomialQMatrixHom k := by
  apply generatedFourth_lift_q_hom_ext
  · intro j
    have hc := generatedFourth_monomial_q_basis_certificates k j
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change toAdd (spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1
        (xiSpinBinaryBasisLift j)).base = _
      rw [generatedFourth_monomial_corrected_q_image, generatedFourth_monomial_q_matrix_value]
      simpa only [xiSpinBinaryBasisLift, toAdd_ofAdd, Matrix.mulVec_single_one] using hc.1
    · apply toAdd.injective
      change toAdd (spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1
        (xiSpinBinaryBasisLift j)).coeff = _
      rw [generatedFourth_monomial_corrected_q_image, generatedFourth_monomial_q_matrix_value]
      simpa only [xiSpinBinaryBasisLift, toAdd_ofAdd, toAdd_one, zero_add,
        generatedFourthLiftQMatrixPhase, Matrix.toBilin'_single] using hc.2
  · change spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1
      qCentralInvolution = _
    rw [show qCentralInvolution = qCentral 1 from rfl, spinConjugation_central]
    apply NormalizedCocycleExtension.Extension.ext
    · rw [generatedFourth_monomial_q_matrix_value]
      simp [qCentral]
    · rw [generatedFourth_monomial_q_matrix_value]
      simp [qCentral, generatedFourthLiftQMatrixPhase]

/-- Complete original full-Q conjugation has the certified literal matrices and central phase. -/
theorem generatedFourth_monomial_q_matrix_action (k : Fin 4) (q : Q) :
    spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1 q =
      generatedFourthMonomialQMatrixHom k q :=
  DFunLike.congr_fun (generatedFourth_monomial_q_matrix_hom k) q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
