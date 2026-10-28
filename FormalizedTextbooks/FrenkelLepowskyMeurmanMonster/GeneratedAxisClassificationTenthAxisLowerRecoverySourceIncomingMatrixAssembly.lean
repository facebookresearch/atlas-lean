/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceIncomingMatrixGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceCache

/-! Ungated exact original incoming matrix binding. No representative orientation is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual source rational matrix discharges the full incoming calibration interface. -/
theorem generatedTenth_source_incoming_matrix_calibration :
    GeneratedTenthFinalShortSourceMatrixCalibration generatedTenthSourceIncomingMatrix :=
  generatedTenth_source_incoming_matrix_entry

/-- The genuine final short formula needs its complete incoming C source certificate. -/
theorem generatedTenth_source_incoming_matrix_final_formula
    (hin : GeneratedTenthRootTwoIncomingShortCertificate) (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortSourceFormula generatedTenthSourceIncomingMatrix r : ℝ) :=
  generatedTenth_final_short_source_formula_actual hin generatedTenthSourceIncomingMatrix
    generatedTenth_source_incoming_matrix_entry r

/-- Complete final cache values and incoming C remain explicit; matrix calibration is proved. -/
theorem generatedTenth_source_incoming_matrix_final_cache
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (cache : Array ℤ)
    (hcache : GeneratedTenthFinalShortSourceCacheCertificate
      generatedTenthSourceIncomingMatrix cache)
    (r : GriessShortIndex) :
    (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortSourceCacheCoefficient cache r : ℝ) / 128 :=
  generatedTenth_final_short_source_cache_coefficient hin generatedTenthSourceIncomingMatrix
    generatedTenth_source_incoming_matrix_calibration cache hcache r

/-- A complete literal cache equality discharges the same incoming calibration interface. -/
theorem generatedTenth_source_incoming_matrix_literal_calibration
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hM : ∀ i j, M i j = generatedTenthSourceIncomingMatrix i j) :
    GeneratedTenthFinalShortSourceMatrixCalibration M :=
  generatedTenth_source_incoming_matrix_literal M hM

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
