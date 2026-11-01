/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompatibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectSourceBinaryData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! The genuine oriented lattice lifts retain the precise original Conway source classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every actual binary vector of the candidate is the genuine transported whole source action. -/
theorem generatedNinth_lower_spin_direct_source_binary (i : Fin 11) :
    leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) =
      leechBinaryAction (generatedNinthAffineLowerTransportedIsometry i) := by
  apply LinearEquiv.ext
  intro v
  apply (leechBinaryAction generatedNinthAffineTransport).injective
  have h : leechBinaryAction generatedNinthAffineTransport
      (leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) v) =
      leechBinaryAction (generatedNinthAffineLowerSourceIsometry i)
        (leechBinaryAction generatedNinthAffineTransport v) := by
    rw [generatedNinth_lower_spin_direct_isometry_binary,
      generatedNinth_affine_transport_binary_action,
      generatedNinth_affine_lower_source_binary,
      generatedNinth_affine_transport_binary_action,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      generatedNinth_lower_spin_direct_source_binary_certificate]
  rw [generatedNinthAffineLowerTransportedIsometry, map_mul, map_mul, map_inv]
  change leechBinaryAction generatedNinthAffineTransport
      (leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) v) =
    leechBinaryAction generatedNinthAffineTransport
      ((leechBinaryAction generatedNinthAffineTransport).symm
        (leechBinaryAction (generatedNinthAffineLowerSourceIsometry i)
          (leechBinaryAction generatedNinthAffineTransport v)))
  rw [LinearEquiv.apply_symm_apply]
  exact h

/-- Faithfulness identifies precisely the actual original source Conway class. -/
theorem generatedNinth_lower_spin_direct_source_class (i : Fin 11) :
    (QuotientGroup.mk (generatedNinthLowerSpinDirectIsometry i) : Co1) =
      (QuotientGroup.mk (generatedNinthAffineLowerTransportedIsometry i) : Co1) := by
  apply co1BinaryAction_injective
  change leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) =
    leechBinaryAction (generatedNinthAffineLowerTransportedIsometry i)
  exact generatedNinth_lower_spin_direct_source_binary i

/-- Each genuine local lift projects to the corresponding actual original lower source class. -/
theorem generatedNinth_lower_spin_direct_projection_eq_original (i : Fin 11) :
    projH (generatedNinthLowerSpinDirectLocal i) =
      (QuotientGroup.mk (generatedNinthAffineLowerTransportedIsometry i) : Co1) :=
  generatedNinth_lower_spin_direct_source_class i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
