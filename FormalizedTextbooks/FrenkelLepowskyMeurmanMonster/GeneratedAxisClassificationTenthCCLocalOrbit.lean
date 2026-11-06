/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCFiniteCertificateCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateCAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalSourceCertificateTAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryIncomingBPackedCertificatesActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryStartWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCBoundaryFinishWords

/-! The exact local stabilizer and orbit of the original Tenth axis (source Table 1 position 12).
The complete finite final C/T, incoming B and C support certificates, together with the tabulated
tensor boundary certificates, discharge every premise, so both genuine fibers fix the whole axis
and attain the matrix quotient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both genuine fibers fix the whole canonical axis, with every finite certificate proved. -/
theorem generatedTenth_actual_two_fixers (g : Fin 2) :
    rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis :=
  generatedTenth_finite_certificates_two_fixers generatedTenth_final_source_certificate_C_all
    generatedTenth_final_source_certificate_T_all
    generatedTenth_incoming_B_packed_certificates_integer
    generatedTenth_two_fixer_c_support_certificate
    generatedTenth_cc_packed_boundary_bounds generatedTenth_cc_start_words
    generatedTenth_cc_finish_words g

/-- The full actual original Tenth-axis stabilizer in H has exactly 2,903,040 elements. -/
theorem generatedTenth_actual_local_axis_stabilizer_card :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 :=
  generatedTenth_source_compact_canonical_original_card generatedTenth_actual_two_fixers

/-- The genuine Tenth-axis orbit under H has exactly 48,057,153,579,122,688,000 elements. -/
theorem generatedTenth_actual_local_axis_orbit_card :
    Nat.card (MulAction.orbit H generatedTenthAxis) = 48057153579122688000 :=
  generatedTenth_local_axis_orbit_card_of_stabilizer_card
    generatedTenth_actual_local_axis_stabilizer_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
