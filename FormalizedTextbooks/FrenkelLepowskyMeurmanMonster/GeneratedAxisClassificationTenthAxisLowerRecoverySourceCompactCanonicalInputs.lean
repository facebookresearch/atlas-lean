/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalFinalSourceActual

/-! New canonical compact-source endpoints. All proof bodies remain uncompiled drafts.
The complete incoming B calibration is explicit; original source tensor orientation is unused. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All preferred short coefficients of the canonical axis, with all zero addresses retained. -/
def GeneratedTenthSourceCompactCanonicalCInputCondition : Prop :=
  ∀ r, 128 * (griessConwayEncode generatedTenthSourceCompactAxis).2.1 r =
    (generatedTenthFinalShortPackedCacheCoefficient r : ℝ)

/-- All physical tensor coordinates of the canonical axis in the exact scale512sqrt2. -/
def GeneratedTenthSourceCompactCanonicalTInputCondition : Prop :=
  ∀ k i, 512 * Real.sqrt 2 * (griessConwayEncode generatedTenthSourceCompactAxis).2.2
    (golayLabelCoefficients k) i = (generatedTenthTwoFixerTensorInput k i : ℝ)

/-- The unchanged complete finite C predicate binds the canonical short cache. -/
theorem generatedTenth_source_compact_canonical_C_input
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (hB : GeneratedTenthSourceCompactCanonicalBCondition)
    (hC : ∀ a, GeneratedTenthFinalSourceCertificateC a) :
    GeneratedTenthSourceCompactCanonicalCInputCondition := by
  intro r
  have h := hC (generatedNinthLowerSpinShortAddress r)
  simp only [GeneratedTenthFinalSourceCertificateC,
    generatedNinth_lower_spin_short_index_address] at h
  rw [generatedTenth_source_compact_canonical_final_C_integer hin hB r, h]
  rfl

/-- The unchanged complete interleaved finite T predicate binds every canonical tensor input. -/
theorem generatedTenth_source_compact_canonical_T_input
    (hin : GeneratedTenthRootTwoIncomingShortCertificate)
    (hB : GeneratedTenthSourceCompactCanonicalBCondition)
    (hT : ∀ a, GeneratedTenthFinalSourceCertificateT a) :
    GeneratedTenthSourceCompactCanonicalTInputCondition := by
  intro k i
  rw [generatedTenth_source_compact_canonical_final_T_integer hin hB k i,
    generatedTenth_final_source_certificate_T_coordinates hT k i]

/-- Genuine orbit equivalence transfers a canonical stabilizer count to the original axis. -/
theorem generatedTenth_source_compact_canonical_count_transfer
    (hcard : Nat.card generatedTenthSourceCompactAxisStabilizer = 2903040) :
    Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040 := by
  rw [← generatedTenth_source_compact_axis_stabilizer_card]
  exact hcard

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
