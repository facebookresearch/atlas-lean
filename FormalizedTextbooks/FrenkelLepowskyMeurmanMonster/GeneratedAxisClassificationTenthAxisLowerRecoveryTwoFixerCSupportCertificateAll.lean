/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateCoverageAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateFixer00All
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateFixer01All

/-! Ungated exact candidate support data/certificates; numerical parsing is not proof. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The unchanged complete support condition holds for both required genuine fibers. -/
theorem generatedTenth_two_fixer_c_support_certificate (g : Fin 2) :
    GeneratedTenthTwoFixerCSupportCondition g
      (generatedTenthTwoFixerCSupportDestination g) (generatedTenthTwoFixerCSupportPhase g) := by
  apply generatedTenth_two_fixer_c_support_condition_of_rows g
    generatedTenth_two_fixer_c_support_coverage_all
  fin_cases g
  · exact generatedTenth_two_fixer_c_support_rows_00
  · exact generatedTenth_two_fixer_c_support_rows_01

/-- Full actual C fixation follows only after the complete actual source-cache calibration. -/
theorem generatedTenth_two_fixer_c_support_actual (g : Fin 2)
    (hsource : GeneratedTenthTwoFixerCSourceCacheCondition) :
    localShortRepresentation (generatedTenthTwoFixerCFiber g)
      (griessConwayEncode generatedTenthAxis).2.1 =
        (griessConwayEncode generatedTenthAxis).2.1 :=
  generatedTenth_two_fixer_c_short_fix g
    (generatedTenthTwoFixerCSupportDestination g) (generatedTenthTwoFixerCSupportPhase g)
    hsource (generatedTenth_two_fixer_c_support_certificate g)

/-- All zero coefficients are retained by the genuine permutation as a proved consequence. -/
theorem generatedTenth_two_fixer_c_support_actual_complement (g : Fin 2)
    (hsource : GeneratedTenthTwoFixerCSourceCacheCondition) :
    GeneratedTenthTwoFixerCComplementCondition g :=
  generatedTenth_two_fixer_c_complement g
    (generatedTenthTwoFixerCSupportDestination g) (generatedTenthTwoFixerCSupportPhase g)
    hsource (generatedTenth_two_fixer_c_support_certificate g)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
