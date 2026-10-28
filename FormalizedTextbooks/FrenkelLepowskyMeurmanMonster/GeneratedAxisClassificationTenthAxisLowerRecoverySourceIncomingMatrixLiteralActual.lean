/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceIncomingMatrixLiteralCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceIncomingMatrixAssembly

/-! Ungated complete literal original Root02 rational matrix source cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The complete literal matrix cache has the genuine original incoming packet calibration. -/
theorem generatedTenth_source_incoming_matrix_literal_actual :
    GeneratedTenthFinalShortSourceMatrixCalibration generatedTenthSourceIncomingMatrixLiteral :=
  generatedTenth_source_incoming_matrix_literal_calibration
    generatedTenthSourceIncomingMatrixLiteral
      generatedTenth_source_incoming_matrix_literal_certificate

/-- Every final Tenth short coefficient can use the literal incoming matrix cache. -/
theorem generatedTenth_source_incoming_matrix_literal_final_formula
    (hin : GeneratedTenthRootTwoIncomingShortCertificate) (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortSourceFormula generatedTenthSourceIncomingMatrixLiteral r : ℝ) :=
  generatedTenth_final_short_source_formula_actual hin generatedTenthSourceIncomingMatrixLiteral
    generatedTenth_source_incoming_matrix_literal_actual r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
