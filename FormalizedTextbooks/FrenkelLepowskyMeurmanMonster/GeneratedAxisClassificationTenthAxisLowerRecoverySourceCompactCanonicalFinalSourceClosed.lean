/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateCAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateTAll

/-! New canonical compact-source endpoints. All proof bodies remain uncompiled drafts.
The complete incoming B calibration is explicit; original source tensor orientation is unused. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Existing complete C and T finite joins leave precisely the canonical B source binding. -/
theorem generatedTenth_source_compact_canonical_final_inputs
    (hB : GeneratedTenthSourceCompactCanonicalBCondition) :
    GeneratedTenthSourceCompactCanonicalCInputCondition ∧
      GeneratedTenthSourceCompactCanonicalTInputCondition := by
  constructor
  · exact generatedTenth_source_compact_canonical_C_input
      generatedTenth_root_two_certificates_all hB generatedTenth_final_source_certificate_C_all
  · exact generatedTenth_source_compact_canonical_T_input
      generatedTenth_root_two_certificates_all hB generatedTenth_final_source_certificate_T_all

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
