/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactQCertificatesAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointQCertificatesAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactSpatialBinaryAll
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointSpatialBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionGeneric

/-! Ungated compatible fibers for the literal joint9*1 and original10 projected generators.
Compatibility uses held genuine full-Q and spatial certificates. Whole-axis fixation is separate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The joint spin cache and literal actual spatial product nine times one form a real fiber. -/
def generatedTenthTwoFixerJointFiber : localFiberSubgroup :=
  generatedTenthJointQCertificatesFiber generatedTenth_joint_spatial_binary_zero

/-- The original10 spin cache and actual original10 spatial map form a real fiber. -/
def generatedTenthTwoFixerOriginalTenFiber : localFiberSubgroup :=
  generatedTenthCompact10QCertificatesFiber (generatedTenth_compact_spatial_binary_all 10)

/-- The original multiplication order is retained by the joint spatial component. -/
theorem generatedTenth_two_fixer_joint_spatial :
    generatedTenthTwoFixerJointFiber.val.2 =
      generatedTenthAxisLowerRecoveryCompactSpatial 9 *
        generatedTenthAxisLowerRecoveryCompactSpatial 1 := by
  rfl

/-- The compatible joint fiber projects to the genuine first two-generator source. -/
theorem generatedTenth_two_fixer_joint_projection :
    projH (localFiberIntoH generatedTenthTwoFixerJointFiber) =
      generatedTenthAxisLowerRecoveryTwoProjectionActual 0 := by
  rfl

/-- The compatible original10 fiber projects to the genuine second two-generator source. -/
theorem generatedTenth_two_fixer_original_ten_projection :
    projH (localFiberIntoH generatedTenthTwoFixerOriginalTenFiber) =
      generatedTenthAxisLowerRecoveryTwoProjectionActual 1 := by
  rfl

/-- Both actual whole-axis fixer hypotheses supply genuine attained projection memberships. -/
theorem generatedTenth_two_fixer_projected_mem
    (hjoint : rhoLocal (localFiberIntoH generatedTenthTwoFixerJointFiber)
      generatedTenthAxis = generatedTenthAxis)
    (hten : rhoLocal (localFiberIntoH generatedTenthTwoFixerOriginalTenFiber)
      generatedTenthAxis = generatedTenthAxis)
    (g : Fin 2) :
    generatedTenthAxisLowerRecoveryTwoProjectionActual g ∈
      generatedTenthProjectedAxisStabilizer := by
  fin_cases g
  · refine ⟨⟨localFiberIntoH generatedTenthTwoFixerJointFiber, hjoint⟩, ?_⟩
    exact generatedTenth_two_fixer_joint_projection
  · refine ⟨⟨localFiberIntoH generatedTenthTwoFixerOriginalTenFiber, hten⟩, ?_⟩
    exact generatedTenth_two_fixer_original_ten_projection

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

