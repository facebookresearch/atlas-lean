/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceTensorCalibration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! A genuine compact source fiber retains the explicit spatial word without selecting
the scalar orientation of the original source spin. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

private theorem binary_of_conjugation_eq (a b : SpinHolomorph)
    (h : spinConjugation a = spinConjugation b) :
    spinBinaryAction a = spinBinaryAction b :=
  congrArg qBinaryAction h

private theorem binary_of_quotient_eq (a b : leechIsomSubgroup)
    (h : QuotientGroup.mk' signsSubgroup a = QuotientGroup.mk' signsSubgroup b) :
    leechBinaryAction a = leechBinaryAction b := by
  have hc := congrArg co1BinaryAction h
  simpa only [co1BinaryAction, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] using hc

private theorem fiber_tensor_factors (f : localFiberSubgroup) :
    localTensorRepresentation f = coordinateGLTransport conwayTensorCoordinates
      (TensorProduct.congr f.val.1.val f.val.2.val) := rfl

/-- Full original Q equality and actual Co1 equality certify the chosen compact fiber. -/
theorem generatedTenth_source_compact_fiber_compatible :
    spinBinaryAction (generatedTenthAxisLowerRecoverySourceCompactSpin 0) =
      leechBinaryAction (generatedAxisGlobalFifthShortSpatialWord 2) := by
  have hs := binary_of_conjugation_eq
    ((generatedAxisGlobalFifthShortWordFiber 2).val.1)
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0)
    (MulEquiv.ext generatedTenth_source_q_certificates_original_Q_eq)
  have hv := binary_of_quotient_eq
    ((generatedAxisGlobalFifthShortWordFiber 2).val.2)
    (generatedAxisGlobalFifthShortSpatialWord 2)
    generatedTenth_axis_lower_recovery_source_spatial_quotient
  exact hs.symm.trans ((generatedAxisGlobalFifthShortWordFiber 2).property.trans hv)

/-- The compact spin and explicit original spatial word form an actual local fiber. -/
@[irreducible] def generatedTenthSourceCompactFiber : localFiberSubgroup :=
  ⟨(generatedTenthAxisLowerRecoverySourceCompactSpin 0,
    generatedAxisGlobalFifthShortSpatialWord 2), generatedTenth_source_compact_fiber_compatible⟩

/-- Both actual components of the compact source fiber retain their specified orientation. -/
theorem generatedTenth_source_compact_fiber_components :
    generatedTenthSourceCompactFiber.val =
      (generatedTenthAxisLowerRecoverySourceCompactSpin 0,
        generatedAxisGlobalFifthShortSpatialWord 2) := by
  unfold generatedTenthSourceCompactFiber
  rfl

/-- The genuine compact fiber's tensor action is the previously specified compact action. -/
theorem generatedTenth_source_compact_fiber_tensor :
    localTensorRepresentation generatedTenthSourceCompactFiber =
      generatedTenthAxisLowerRecoverySourceCompactTensor := by
  rw [fiber_tensor_factors, generatedTenth_source_compact_fiber_components]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
