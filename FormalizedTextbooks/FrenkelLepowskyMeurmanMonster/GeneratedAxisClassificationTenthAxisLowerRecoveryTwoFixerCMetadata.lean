/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQMaskGeneric

/-! Ungated finite metadata proof drafts. The reused Q theorem is polymorphic in MulAut Q. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- These unit images are the held genuine full-Q images, with both source phases intact. -/
theorem generatedTenth_two_fixer_c_units (g : Fin 2) (j : Fin 24) :
    spinConjugation (generatedTenthTwoFixerCFiber g).val.1 (qCoordinateGenerator j) =
      generatedTenthTwoFixerCUnitImages g j := by
  fin_cases g
  · change spinConjugation (generatedTenthAxisLowerRecoveryJointCompactSpin 0)
      (qCoordinateGenerator j) = generatedTenthAxisLowerRecoveryJointCompactFullQCache 0 j
    rw [generatedTenth_axis_lower_recovery_joint_compact_conjugation]
    exact generatedTenth_joint_q_certificates_all j
  · change spinConjugation (generatedTenthAxisLowerRecoveryCompactSpin 10)
      (qCoordinateGenerator j) = generatedTenthAxisLowerRecoveryCompactFullQCache 10 j
    rw [generatedTenth_axis_lower_recovery_compact_conjugation]
    exact generatedTenth_compact10_q_certificates_all j

/-- The candidate columns are the complete held unit image base coordinates. -/
theorem generatedTenth_two_fixer_c_metadata_base (g : Fin 2) (j : Fin 24) :
    toAdd (generatedTenthTwoFixerCUnitImages g j).base =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthTwoFixerCColumns g j) := by
  fin_cases g <;> rfl

set_option maxHeartbeats 4000000 in
-- Bound the complete 2 by 24 by 24 cocycle-bit check.
/-- Every row bit must equal the actual original upper triangular cocycle difference. -/
theorem generatedTenth_two_fixer_c_metadata_rows : ∀ (g : Fin 2) (i j : Fin 24),
    monsterCo1GeometryBinaryMaskDecode (generatedTenthTwoFixerCRows g i) j =
      if i < j then
        qBeta (monsterCo1GeometryBinaryMaskDecode (generatedTenthTwoFixerCColumns g i))
          (monsterCo1GeometryBinaryMaskDecode (generatedTenthTwoFixerCColumns g j)) +
            qBeta (Pi.single i 1) (Pi.single j 1) else 0 := by
  decide +kernel

/-- All48 original unit central bits must bind the candidate correction masks. -/
theorem generatedTenth_two_fixer_c_metadata_coefficients : ∀ (g : Fin 2) (i : Fin 24),
    monsterCo1GeometryBinaryMaskDecode (generatedTenthTwoFixerCCoefficients g) i =
      toAdd (generatedTenthTwoFixerCUnitImages g i).coeff := by
  decide +kernel

/-- Genuine fiber compatibility supplies the actual square-form preservation hypothesis. -/
theorem generatedTenth_two_fixer_c_square (g : Fin 2) (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction (spinConjugation (generatedTenthTwoFixerCFiber g).val.1) v) =
      squareQuad v := by
  change squareQuad (spinBinaryAction (generatedTenthTwoFixerCFiber g).val.1 v) = _
  rw [(generatedTenthTwoFixerCFiber g).property]
  exact leechBinaryAction_squareQuad _ v

/-- All masks, including the original central cochain, are the genuine source automorphism. -/
theorem generatedTenth_two_fixer_c_mask_actual (g : Fin 2) (v : ℕ) :
    spinConjugation (generatedTenthTwoFixerCFiber g).val.1 (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedTenthTwoFixerCColumns g)
        (generatedTenthTwoFixerCRows g) (generatedTenthTwoFixerCCoefficients g) v :=
  generatedNinth_lower_spin_q_mask_from_units _
    (generatedTenth_two_fixer_c_square g) (generatedTenthTwoFixerCUnitImages g)
    (generatedTenthTwoFixerCColumns g) (generatedTenthTwoFixerCRows g)
    (generatedTenthTwoFixerCCoefficients g) (generatedTenth_two_fixer_c_units g)
    (generatedTenth_two_fixer_c_metadata_base g) (generatedTenth_two_fixer_c_metadata_rows g)
    (generatedTenth_two_fixer_c_metadata_coefficients g) v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

