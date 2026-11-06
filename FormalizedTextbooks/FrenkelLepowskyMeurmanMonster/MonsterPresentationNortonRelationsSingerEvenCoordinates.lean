/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual even cocode and central checks for the Singer-triality commutator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerCommutator

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The physical Singer pullback preserves actual even cocode parity. -/
theorem monsterNortonSinger_pullback_even (δ : SpinIndex) (hδ : δ 11 = 0) :
    monsterMonomialPullback (monsterNortonSingerCode 0).symm δ 11 = 0 := by
  change spinDot δ ((monsterNortonSingerCode 0).symm (Pi.single 11 1)) = 0
  have ho : (monsterNortonSingerCode 0).symm (Pi.single 11 1) = Pi.single 11 1 := by
    decide +kernel
  rw [ho, spinDot_single_right, hδ]

/-- Every genuine even source cocode commutes with the actual Singer-triality commutator. -/
theorem monsterNortonSinger_commutator_even (δ : SpinIndex) (hδ : δ 11 = 0) :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated (sourceQCocode δ)) := by
  have hx := monsterNortonSingerLocal_generated_conjugate_Q (sourceQCocode δ)
  rw [monsterNortonSingerImage_cocode] at hx
  simpa only [map_inv] using
    monsterNortonSinger_commutator_commutes_of_triality_commutation
      (localIntoGenerated monsterNortonSingerLocal) extraIntoGenerated
      (qIntoGenerated (sourceQCocode δ))
      (qIntoGenerated (sourceQCocode
        (monsterMonomialPullback (monsterNortonSingerCode 0).symm δ))) hx
      (monsterNortonEvenCocode_generated_commute_extra δ hδ)
      (monsterNortonEvenCocode_generated_commute_extra _
        (monsterNortonSinger_pullback_even δ hδ))

private theorem singer_central_commute (k : Fin 3) :
    Commute (localIntoGenerated monsterNortonSingerLocal) (centralSignIntoGenerated k) := by
  have hz := monsterNortonSingerLocal_generated_conjugate_Q qCentralInvolution
  have ho := monsterNortonSingerLocal_generated_conjugate_Q sourceOmegaQ
  rw [monsterNortonSingerCentral_certificate] at hz
  rw [monsterNortonSingerOmega_certificate, qIntoGenerated_sourceOmegaQ] at ho
  have hzg : qIntoGenerated qCentralInvolution = centralSignIntoGenerated 0 := by
    apply Subtype.ext
    exact localCentralGriess_eq_trialityCentralSign
  rw [hzg] at hz
  have hzc : Commute (localIntoGenerated monsterNortonSingerLocal)
      (centralSignIntoGenerated 0) := mul_inv_eq_iff_eq_mul.mp hz
  have hoc : Commute (localIntoGenerated monsterNortonSingerLocal)
      (centralSignIntoGenerated 2) := mul_inv_eq_iff_eq_mul.mp ho
  fin_cases k
  · exact hzc
  · have h12 : centralSignIntoGenerated 0 * centralSignIntoGenerated 1 =
        centralSignIntoGenerated 2 := by
      apply Subtype.ext
      exact trialityCentralSign_zero_mul_one
    have h1 : centralSignIntoGenerated 1 =
        (centralSignIntoGenerated 0)⁻¹ * centralSignIntoGenerated 2 := by
      rw [← h12]
      group
    change Commute (localIntoGenerated monsterNortonSingerLocal) (centralSignIntoGenerated 1)
    rw [h1]
    exact hzc.inv_right.mul_right hoc
  · exact hoc

/-- The genuine Singer-triality commutator commutes with the full source central involution. -/
theorem monsterNortonSinger_commutator_central :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated qCentralInvolution) := by
  have hzg : qIntoGenerated qCentralInvolution = centralSignIntoGenerated 0 := by
    apply Subtype.ext
    exact localCentralGriess_eq_trialityCentralSign
  rw [hzg]
  apply (show Commute ((localIntoGenerated monsterNortonSingerLocal)⁻¹ *
    extraIntoGenerated⁻¹ * localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
      (centralSignIntoGenerated 0) from ?_)
  apply monsterNortonSinger_commutator_commutes_of_covariance _ _ _
    (centralSignIntoGenerated 0)
  · exact mul_inv_eq_iff_eq_mul.mpr (singer_central_commute 0).eq
  · have he : extraIntoGenerated * centralSignIntoGenerated 0 * extraIntoGenerated⁻¹ =
        centralSignIntoGenerated 1 := by
      apply Subtype.ext
      change sExtra * trialityCentralSign 0 * sExtra⁻¹ = trialityCentralSign 1
      rw [← localCentralGriess_eq_trialityCentralSign]
      exact localCentralGriess_conjugate
    rw [he]
    exact mul_inv_eq_iff_eq_mul.mpr (singer_central_commute 1).eq

/-- The genuine Singer-triality commutator commutes with the full preferred all-one lift. -/
theorem monsterNortonSinger_commutator_omega :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated sourceOmegaQ) := by
  rw [qIntoGenerated_sourceOmegaQ]
  apply (show Commute ((localIntoGenerated monsterNortonSingerLocal)⁻¹ *
    extraIntoGenerated⁻¹ * localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
      (centralSignIntoGenerated 2) from ?_)
  apply monsterNortonSinger_commutator_commutes_of_covariance _ _ _
    (centralSignIntoGenerated 2)
  · exact mul_inv_eq_iff_eq_mul.mpr (singer_central_commute 2).eq
  · have he : extraIntoGenerated * centralSignIntoGenerated 2 * extraIntoGenerated⁻¹ =
        centralSignIntoGenerated 0 := by
      apply Subtype.ext
      change sExtra * trialityCentralSign 2 * sExtra⁻¹ = trialityCentralSign 0
      simpa only [show trialityCycle 2 = 0 by decide] using trialityCentralSign_conjugate 2
    rw [he]
    exact mul_inv_eq_iff_eq_mul.mpr (singer_central_commute 0).eq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
