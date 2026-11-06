/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortCertificatesAll

/-! Ungated assembly of the complete original Root02 incoming short coefficient certificate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete actual short component, retaining every preferred phase and outside zero. -/
theorem generatedTenth_root_two_incoming_short_source_actual (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal
      (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2)) generatedFifthAxis)).2.1 r =
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r : ℝ) / 16 :=
  generatedTenth_root_two_incoming_short_actual generatedTenth_root_two_certificates_all r

/-- All original incoming odd columns use the same complete source certificate. -/
theorem generatedTenth_root_two_incoming_short_source_odd_actual
    (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (rhoLocal
      (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2)) generatedFifthAxis)).2.1
      (Sum.inr (Sum.inr (d, i))) =
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortIncomingCoefficient d i : ℝ) / 16 :=
  generatedTenth_root_two_incoming_short_odd_actual generatedTenth_root_two_certificates_all d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
